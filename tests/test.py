from colorprint import colorprint as cprint 
import subprocess
import os

EXECUTABLE_PATH = "./_build/default/bin/pieuvre.exe"

def test_should_fail(file):
    with open(file, "r") as f:
        fouine_result = subprocess.run(
            [EXECUTABLE_PATH, file],
            stdin=f,
            capture_output=True,
            text=True,
        )

    ok = fouine_result.stderr != "" or fouine_result.returncode != 0

    if ok:
        cprint(f"Test {file} passed", "green")
    else:
        cprint(f"No error in {file}", "red")

    return ok

def test_should_be_ok(file):
    with open(file, "r") as f:
        fouine_result = subprocess.run(
            [EXECUTABLE_PATH, file],
            stdin=f,
            capture_output=True,
            text=True,
        )

    ok = (
        fouine_result.returncode == 0
    )

    if ok:
        cprint(f"Test {file} passed", "green")
    else:
        cprint(f"Error in {file}", "red")
        cprint(f"Stdout : {fouine_result.stdout}", "red")
        cprint(f"Stderr : {fouine_result.stderr}", "red")

    return ok

cprint("Building Project", "green")
try:
    caml_result = subprocess.run(
        ["dune", "build"],
        check=True
    )
except subprocess.CalledProcessError as e:
    cprint("Error building project", "red")
cprint("Project successfuly build", "green")
cprint("")

ml_files = [
    os.path.join(root, f)
    for root, dirs, files in os.walk("tests")
    for f in files
    if f.endswith(".8pus") and "temp.8pus" not in f 
    and "ShouldFail" not in root.split(os.sep)
]

should_fail_files = [
    os.path.join(root, f)
    for root, dirs, files in os.walk("tests")
    for f in files
    if f.endswith(".8pus") and "temp.8pus" not in f
    and "ShouldFail" in root.split(os.sep)
]

nb_test = len(ml_files) + len(should_fail_files)

total = 0
for file in ml_files:
    total += test_should_be_ok(file)
for file in should_fail_files:
    total += test_should_fail(file)

print()
if total == nb_test:
    cprint(f"All {total} test passed !!", "green")
else:
    cprint(f"Some tests didnt pass : ({total}/{nb_test} correct).", "red")
