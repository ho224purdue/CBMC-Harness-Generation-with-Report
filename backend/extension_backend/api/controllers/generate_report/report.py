import os
import subprocess
import json
import pandas as pd

def go_up_directories(start_path, levels=1):
    """Move up `levels` directories from `start_path`."""
    path = os.path.abspath(start_path)
    for _ in range(levels):
        path = os.path.dirname(path)
    return path

def get_sibling_dir(current_abs_path, sibling_name):
    """Get the absolute path of a sibling directory."""
    # Step 1: Get the parent directory of the current path
    parent_dir = os.path.dirname(current_abs_path)
    
    # Step 2: Join parent directory with the sibling's name
    sibling_dir = os.path.join(parent_dir, sibling_name)
    
    # Step 3: Normalize the path (resolve "..", ".", etc.)
    return os.path.normpath(sibling_dir)

def generate_report(workspace, result):
    harnessName = result["name"]
    harness = result["generated_harness"]
    os.chdir(go_up_directories(__file__, levels=4))  # Move up 5 directories
    current_dir = os.getcwd()
    os.chdir(get_sibling_dir(current_dir, "cbmc/" + workspace + "/test/cbmc/proofs"))
    functions_set = set(os.listdir())
    functionName = harnessName[: 0 - len("harness") - 1] # clean name without '_harness'
    # search for name of function in ls
    if functionName not in functions_set:
        raise Exception(f"Function was not found in list of functions in {os.getcwd()}")
    os.chdir(get_sibling_dir(os.getcwd(), "proofs/" + functionName)) # navigate into directory
    previous_lines = []
    with open(harnessName + ".c", "r") as f:
        for line in f:
            if harnessName + "()" in line:
                break
            previous_lines.append(line)
    previous_str = ''.join(previous_lines)
    new_harness = previous_str + harness # create new harness through concatenation
    # write into file
    with open(harnessName + ".c", "w") as f:
        f.write(new_harness)
    # also return generated + concatenated new harness
    result["generated_harness"] = new_harness
    # now run the script
    os.chdir("..")
    try:
        output = subprocess.run(
            ["./run-cbmc-proofs.py", "--proofs", functionName],
            capture_output=True,
            text=True,
            check=True
        )
        print("Run successful!\n", output.stdout)
        # parse JSON
        # Get the proof directory path
        proof_dir = os.path.join(os.getcwd(), functionName)
        json_dir = os.path.join(proof_dir, "json")
        
        # Initialize coverage data structure
        coverage_data = {
            'Function': functionName,
            'Number of reported errors': 0,
            'Total coverage': 0.0,
            'Coverage of harnessed function': 0.0,
            'Total reachable lines': 0,
            'Reachable lines harnessed': 0
        }

        # Process JSON files if they exist
        json_files = {
            'result': 'viewer-result.json',
            'coverage': 'viewer-coverage.json',
            'property': 'viewer-property.json'
        }

        if os.path.exists(json_dir):
            # Load JSON data
            data = {}
            for key, fname in json_files.items():
                path = os.path.join(json_dir, fname)
                if os.path.exists(path):
                    with open(path, 'r') as f:
                        data[key] = json.load(f)

            # Process error counts
            if 'result' in data:
                false_entries = set()
                for entry in data['result']["viewer-result"]['results']['false']:
                    if "no-body" not in entry and "unwind" not in entry:
                        prop = data['property']["viewer-property"]["properties"][entry]
                        false_entries.add(prop["location"]["line"])
                coverage_data['Number of reported errors'] = len(false_entries)

            # Process coverage data
            if 'coverage' in data:
                cov = data['coverage']["viewer-coverage"]
                coverage_data.update({
                    'Total coverage': cov['overall_coverage']['percentage'],
                    'Total reachable lines': cov['overall_coverage']['total']
                })

                # Find harness-specific coverage
                for func in cov.get('function_coverage', {}):
                    if func.endswith(harnessName):
                        coverage_data['Coverage of harnessed function'] = cov['function_coverage'][func].get('percentage', 0)
                        coverage_data['Reachable lines harnessed'] = cov['function_coverage'][func].get('total', 0)
                        break

        # Add to result
        result["coverage"] = coverage_data
        return result
    except subprocess.CalledProcessError as err:
        # Handle missing executable
        print(f"run-cbmc-proofs.py failed (exit {err.returncode}) while running {err.cmd}\nstdout:\n{err.stdout}\nstderr:\n{err.stderr}")
        if "report" in result:
            result["report"] = result["report"] + f"\n Another error also occurred \n{err}"
        else:
            if "correct" in result:
                result["correct"] = False
            result["report"] = err
        return result
    except Exception as e:
        print(f"Error processing coverage data: {str(e)}")
        if "report" in result:
            result["report"] = result["report"] + f"\n Another error also occurred {e}"
        else:
            if "correct" in result:
                result["correct"] = False
            result["report"] = e
        return result
    
    


    
