const fs = require('fs');
const Parser = require('tree-sitter');
const C = require('tree-sitter-c');

// Initialize tree-sitter-c parser
const parser = new Parser();
// @ts-ignore
parser.setLanguage(C);

/**
 * Recursively traverse the AST to extract:
 *  - Function definitions (function_definition nodes)
 *  - Function calls (call_expression nodes)
 *
 * @param {string} filePath        Path to the current file being parsed
 * @param {object} functionMap     A map of functionName -> fileWhereDefined
 * @param {object} callMatrix      A map of caller -> { callee: 1, ... }
 * @param {Array}  allFunctions    A de-duplicated array of all function names found
 */
function extractFunctionsAndCalls(filePath, functionMap, callMatrix, allFunctions) {
    const sourceCode = fs.readFileSync(filePath, 'utf8');
    const tree = parser.parse(sourceCode);
    const root = tree.rootNode;

    function addFunctionToList(funcName) {
        if (!allFunctions.includes(funcName)) {
            allFunctions.push(funcName);
        }
    }

    function traverse(node, currentFunction = null) {
        if (node.type === 'function_definition') {
            const funcName = node.child(1).text.replace(/\(.*/, '');
            // We assume functionMap is already populated, but let's do safety:
            functionMap[funcName] = filePath;
            addFunctionToList(funcName);

            for (let i = 0; i < node.childCount; i++) {
                traverse(node.child(i), funcName);
            }
        }
        else if (node.type === 'call_expression' && currentFunction) {
            const calledFuncName = node.child(0).text;
            // Only record if it's in functionMap (i.e., locally defined)
            if (functionMap[calledFuncName]) {
                addFunctionToList(calledFuncName);

                if (!callMatrix[currentFunction]) {
                    callMatrix[currentFunction] = {};
                }
                callMatrix[currentFunction][calledFuncName] = 1;
            }

            // Recurse to catch nested
            for (let i = 0; i < node.childCount; i++) {
                traverse(node.child(i), currentFunction);
            }
        }
        else {
            for (let i = 0; i < node.childCount; i++) {
                traverse(node.child(i), currentFunction);
            }
        }
    }

    traverse(root);
}


/**
 * Build an adjacency matrix from the aggregated callMatrix and allFunctions array.
 * @param {Array}  allFunctions   A de-duplicated array of all function names
 * @param {object} callMatrix     A map of caller -> { callee: 1, ... }
 * @returns {{ matrix: number[][], functionIndex: object }}
 */
function buildAdjacencyMatrix(allFunctions, callMatrix) {
    // Create a square matrix of 0s
    let matrix = Array.from({ length: allFunctions.length }, () =>
        Array(allFunctions.length).fill(0)
    );

    // Map each function name to its index in allFunctions
    let functionIndex = {};
    allFunctions.forEach((func, idx) => {
        functionIndex[func] = idx;
    });

    // Fill the matrix
    for (let caller in callMatrix) {
        for (let callee in callMatrix[caller]) {
            let i = functionIndex[caller];
            let j = functionIndex[callee];
            matrix[i][j] = 1; // Mark adjacency
        }
    }
    //   console.log('ADJ:', matrix);
    return { matrix, functionIndex };
}

/**
 * Parse the file at `filePath`, look for a `function_definition` AST node
 * whose identifier matches `functionName`, and return its complete source code.
 *
 * @param {string} filePath      The .c file you want to parse.
 * @param {string} functionName  The function name to look for (e.g. "main", "functionA").
 * @returns {string|null}        The entire text of that function definition, or null if not found.
 */
function extractFunctionCode(filePath, functionName) {
    // 1. Read and parse the file
    const sourceCode = fs.readFileSync(filePath, 'utf8');
    const tree = parser.parse(sourceCode);
    const root = tree.rootNode;

    // 2. Recursively search for a matching function_definition node
    function findFunctionNode(node) {
        if (node.type === 'function_definition') {
            // Typically, `node.child(1)` is the declarator, which might hold the function name
            const declNode = node.child(1).text.replace(/\(.*/, ''); // remove the parameters after
            if (declNode && declNode === functionName) {
                return node; // Found the function definition
            }
        }
        // Otherwise, search all children
        for (let i = 0; i < node.childCount; i++) {
            const found = findFunctionNode(node.child(i));
            if (found) return found;
        }
        return null;
    }

    const funcNode = findFunctionNode(root);
    if (!funcNode) {
        return null;
    }

    // 3. Return the raw text of the function definition node (including the body)
    // `funcNode.text` gives you everything from the return type to the closing brace.
    return funcNode.text;
}

// helper function to only include local functions
function collectLocalFunctions(filePath, functionMap) {
    const sourceCode = fs.readFileSync(filePath, 'utf8');
    const tree = parser.parse(sourceCode);
    const root = tree.rootNode;

    function traverse(node) {
        if (node.type === 'function_definition') {
            const funcName = node.child(1).text.replace(/\(.*/, '');
            functionMap[funcName] = filePath;
        }
        for (let i = 0; i < node.childCount; i++) {
            traverse(node.child(i));
        }
    }

    traverse(root);
}


module.exports = {
    collectLocalFunctions,
    extractFunctionsAndCalls,
    buildAdjacencyMatrix,
    extractFunctionCode
};
