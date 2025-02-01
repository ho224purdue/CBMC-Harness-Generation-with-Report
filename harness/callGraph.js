const path = require('path');
const { getAllCAndHeaderFiles } = require('./getAllCAndHeaderFiles');
const { extractFunctionsAndCalls, buildAdjacencyMatrix } = require('./parserCore');

/**
 * Recursively scans a project directory, parses all .c and .h files,
 * and returns an adjacency matrix + function map + more.
 *
 * @param {string} projectPath Path to the directory containing C code
 * @returns {object} An object with { functionMap, callMatrix, adjacencyMatrix, functionIndex, allFunctions }
 */
function parseProject(projectPath) {
    // Gather .c and .h files from the directory (recursively)
    const allFiles = getAllCAndHeaderFiles(projectPath);

    // Data structures to populate
    let functionMap = {};   // functionName -> fileWhereDefined
    let callMatrix = {};   // caller -> { callee: 1, ... }
    let allFunctions = [];   // a de-duplicated list of all encountered function identifiers (including param combos for calls)

    // Parse each file, building the call matrix
    allFiles.forEach((filePath) => {
        extractFunctionsAndCalls(filePath, functionMap, callMatrix, allFunctions);
    });

    // Build adjacency matrix
    const { matrix, functionIndex } = buildAdjacencyMatrix(allFunctions, callMatrix);

    return {
        functionMap,
        callMatrix,
        adjacencyMatrix: matrix,
        functionIndex,
        allFunctions
    };
}

// Test directly from CLI (example: node parseProject.js my_project)
if (require.main === module) {
    if (process.argv.length < 3) {
        console.error("Usage: node parseProject.js <path-to-project>");
        process.exit(1);
    }

    const projectPath = path.resolve(process.argv[2]);
    const result = parseProject(projectPath);

    // Print out the JSON structure
    console.log(JSON.stringify(result, null, 2));
}

module.exports = {
    parseProject
};
