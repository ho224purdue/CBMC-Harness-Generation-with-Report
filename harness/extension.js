// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
const vscode = require('vscode');
const fs = require('fs');
const path = require('path');

// function to get directory Tree structure of current wd (reference for AST context later on)
function getDirectoryTree(dirPath, options = {}) {
	const {
		ignore = ['.git', 'node_modules'],
		maxDepth = Infinity,
		currentDepth = 0
	} = options;

	let tree = '';

	try {
		if (currentDepth >= maxDepth) return tree;

		const items = fs.readdirSync(dirPath)
			.filter(item => !ignore.includes(item));

		items.forEach((item, index) => {
			const fullPath = path.join(dirPath, item);
			const isLast = index === items.length - 1;
			const prefix = '  '.repeat(currentDepth) + (isLast ? '└── ' : '├── ');

			try {
				const stats = fs.statSync(fullPath);
				tree += prefix + item + '\n';

				if (stats.isDirectory()) {
					tree += getDirectoryTree(fullPath, {
						...options,
						currentDepth: currentDepth + 1
					});
				}
			} catch (err) {
				console.error(`Error processing ${fullPath}: ${err.message}`);
			}
		});

		return tree;
	} catch (err) {
		console.error(`Error reading directory ${dirPath}: ${err.message}`);
		return tree;
	}
}
// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
/**
 * @param {vscode.ExtensionContext} context
 */
function activate(context) {

	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "harness" is now active!');
	// The command has been defined in the package.json file
	// Now provide the implementation of the command with  registerCommand
	// The commandId parameter must match the command field in package.json
	const disposable = vscode.commands.registerCommand('harness.helloworld', function () {
		// The code you place here will be executed every time your command is executed
		// Display a message box to the user
		console.log("Extension Successfully Activated")
		vscode.window.showInformationMessage('Hello World from the harness extension!');
	});
	// generation function
	const generation = vscode.commands.registerCommand('harness.generation', function () {
		console.log('Harness generation called');
		// Usage
		const folderUri = vscode.workspace.workspaceFolders?.[0]?.uri;
		if (!folderUri) {
			vscode.window.showErrorMessage("No workspace folder is open.");
			return;
		}
		// Convert that URI to a standard file system path.
		const workspacePath = folderUri.fsPath;
		// traverse that path to get dir tree structure
		const tree = getDirectoryTree(workspacePath, {
			ignore: ['.git', 'node_modules'],
			maxDepth: 3 // maximum depth is limited to 3 for now
		});
		console.log(tree);
		vscode.window.showInformationMessage("Harness generation function activated");
	});
	// cleanup
	context.subscriptions.push(disposable);
	context.subscriptions.push(generation);
}

// This method is called when your extension is deactivated
function deactivate() { }

module.exports = {
	activate,
	deactivate
}
