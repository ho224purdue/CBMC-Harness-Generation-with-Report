import os
import sys
import json
import subprocess

# List of required  packages to run
REQUIRED_LIBRARIES = ["tree-sitter", "networkx"]
# Function to check and install missing packages
def install_missing_packages():
    for package in REQUIRED_LIBRARIES:
        try:
            __import__(package)
        except ImportError:
            print(f"Installing missing package: {package}")
            subprocess.check_call([sys.executable, "-m", "pip", "install", package])

# Ensure dependencies are installed
install_missing_packages()

# Now import the required packages
import networkx as nx
from tree_sitter import Language, Parser

# Load Tree-Sitter C parser
C_LANGUAGE = Language('tree-sitter-c.so', 'c')
parser = Parser()
parser.set_language(C_LANGUAGE)

function_map = {} # initialize function map
call_graph = nx.DiGraph()

def extract_functions_and_calls(filename):
    with open(filename, "r") as f:
        source_code = f.read()
    
    tree = parser.parse(bytes(source_code, "utf8"))
    root_node = tree.root_node

    def traverse(node, current_func=None):
        if node.type == 'function_definition':
            func_name = node.child(1).text.decode()
            function_map[func_name] = filename
            call_graph.add_node(func_name)
            traverse(node.child(2), func_name)
        
        elif node.type == 'call_expression' and current_func:
            called_func = node.child(0).text.decode()
            call_graph.add_edge(current_func, called_func)

        for child in node.children:
            traverse(child, current_func)

    traverse(root_node)

def parse_project(directory):
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith(".c"):
                filepath = os.path.join(root, file)
                extract_functions_and_calls(filepath)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(json.dumps({"error": "No directory provided"})) # this shouldn't be required since extensions.js will catch no wd error
        sys.exit(1)

    project_path = sys.argv[1]
    parse_project(project_path) # invoke parse project

    output = {
        "function_map": function_map,
        "call_graph": list(call_graph.edges)
    }
    
    print(json.dumps(output)) # returns call graph and function_map
