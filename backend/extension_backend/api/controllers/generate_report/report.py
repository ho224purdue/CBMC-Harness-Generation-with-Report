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
                # Directory containing the JSON files
        results=[]
        # Iterate over each subdirectory in the llm_proofs directory
        path = os.getcwd()
        next_level_dirs = [os.path.join(path, d) for d in os.listdir(path) if os.path.isdir(os.path.join(path, d))]

        for subdir in next_level_dirs:
            path1=subdir
            next2 = [os.path.join(path1, d) for d in os.listdir(path1) if os.path.isdir(os.path.join(path1, d))]
            for subdir2 in next2:
                for subdir3,_,_files in os.walk(subdir2+"/json"):
                    # Construct the full file path
                    file_path = os.path.join(subdir3,'viewer-result.json')
                    file_path1 = os.path.join(subdir3,'viewer-coverage.json')
                    file_path2 = os.path.join(subdir3,'viewer-property.json')
                    # Load JSON data from the file
                    with open(file_path, 'r') as f:
                        data = json.load(f)
                    with open(file_path1, 'r') as f1:
                        data1 = json.load(f1)
                    with open(file_path2, 'r') as f2:
                        data2 = json.load(f2)
                    # Count the number of false entries
                    uniquef = set()
                    uniquet = set()
                    for each in data["viewer-result"]['results']['true']:
                        if("no-body" in each or "unwind" in each):
                            continue
                        uniquet.add(data2["viewer-property"]["properties"][each]["location"]["line"])
                    for each in data["viewer-result"]['results']['false']:
                        if("no-body" in each or "unwind" in each):
                            continue
                        uniquef.add(data2["viewer-property"]["properties"][each]["location"]["line"])
                    false_count = len(uniquef)
                    print(false_count)
                    
                    
                    # Append the results to the list
                    for each in data1["viewer-coverage"]["function_coverage"]:
                        if(each.endswith("harness.c")):
                            for each1 in data1["viewer-coverage"]["function_coverage"][each]:
                                if(each1.endswith("harness")):
                                    store = data1["viewer-coverage"]["function_coverage"][each][each1]
                    
                    current_dir = os.getcwd()
                    print(current_dir)
                    subdir_value = subdir.replace(current_dir+"/", "")
                    print(subdir_value)
                    if "source/core_http_client.c" in data1["viewer-coverage"]["function_coverage"]:
                        coverage_value = data1["viewer-coverage"]["function_coverage"]["source/core_http_client.c"][subdir_value]["percentage"]
                        total_reachable_lines_harnessed = data1["viewer-coverage"]["function_coverage"]["source/core_http_client.c"][subdir_value]["total"]
                    else:
                        coverage_value = 0
                        total_reachable_lines_harnessed = 0

                    # Append the dictionary to results
                    results.append({
                        'Function': subdir_value,
                        'Number of reported errors': false_count,
                        'Total coverage': data1["viewer-coverage"]['overall_coverage']['percentage'],
                        'Coverage of only harnessed function': coverage_value,
                        'Total reachable lines': data1["viewer-coverage"]['overall_coverage']['total'],
                        'Total reachable lines for only harnessed function': total_reachable_lines_harnessed
                    })

        # Create a DataFrame from the results
        df = pd.DataFrame(results)

        # Save the DataFrame to an Excel file
        output_file = r'after.xlsx'
        df.to_excel(output_file, index=False)

        print(f"Excel file with false counts has been generated: {output_file}")
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
    return result
    
    


    
