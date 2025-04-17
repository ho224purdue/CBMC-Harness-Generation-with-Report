import os
import subprocess

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
    except subprocess.CalledProcessError as err:
        # Handle missing executable
        print(err)
        if "report" in result:
            result["report"] = result["report"] + f"\n Another error also occurred \n{err}"
        else:
            if "correct" in result:
                result["correct"] = False
            result["report"] = err
        return result
    return result
    
    


    
