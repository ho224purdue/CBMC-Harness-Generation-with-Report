const fs = require('fs');
const Parser = require('tree-sitter');
const C = require('tree-sitter-c');

// Initialize tree-sitter-c parser
const parser = new Parser();
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

  // Utility to add a new function name into allFunctions if not already present
  function addFunctionToList(funcName) {
    if (!allFunctions.includes(funcName)) {
      allFunctions.push(funcName);
    }
  }

  function traverse(node, currentFunction = null) {
    // Detect a function definition
    if (node.type === 'function_definition') {
      // Typically child(1) is the function declarator/identifier in a simple case
      const funcName = node.child(1).text;

      // Record in functionMap
      functionMap[funcName] = filePath;
      addFunctionToList(funcName);

      // Traverse inside the function body with "currentFunction = funcName"
      for (let i = 0; i < node.childCount; i++) {
        traverse(node.child(i), funcName);
      }
    }
    // Detect a call expression
    else if (node.type === 'call_expression' && currentFunction) {
      const calledFuncName = node.child(0).text; // just include call

      addFunctionToList(calledFuncName);

      // Mark the call in callMatrix
      if (!callMatrix[currentFunction]) {
        callMatrix[currentFunction] = {};
      }
      callMatrix[currentFunction][calledFuncName] = 1;

      // Continue traversing children to catch nested calls
      for (let i = 0; i < node.childCount; i++) {
        traverse(node.child(i), currentFunction);
      }
    }
    // Otherwise, keep recursing
    else {
      for (let i = 0; i < node.childCount; i++) {
        traverse(node.child(i), currentFunction);
      }
    }
  }

  // Start traversing from the root
  traverse(root, null);
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

module.exports = {
  extractFunctionsAndCalls,
  buildAdjacencyMatrix
};
