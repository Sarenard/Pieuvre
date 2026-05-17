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

def test_reduce_should_be_ok(file):
    answer_file = os.path.join(os.path.dirname(file), "term.answer")
    fouine_result = subprocess.run(
        [EXECUTABLE_PATH, "-reduce", file],
        capture_output=True,
        text=True,
    )

    try:
        with open(answer_file, "r") as f:
            expected = f.read().strip()
    except OSError:
        cprint(f"Missing answer file for {file}", "red")
        return False

    stdout_lines = [line.strip() for line in fouine_result.stdout.splitlines() if line.strip() != ""]
    actual = stdout_lines[-1] if stdout_lines else ""

    ok = fouine_result.returncode == 0 and actual == expected

    if ok:
        cprint(f"Reduce test {file} passed", "green")
    else:
        cprint(f"Reduce error in {file}", "red")
        cprint(f"Expected : {expected}", "red")
        cprint(f"Actual : {actual}", "red")
        cprint(f"Stdout : {fouine_result.stdout}", "red")
        cprint(f"Stderr : {fouine_result.stderr}", "red")

    return ok

def test_alpha_should_be_ok(file):
    expected = "true" if "true" in file.split(os.sep) else "false"
    fouine_result = subprocess.run(
        [EXECUTABLE_PATH, "-alpha", file],
        capture_output=True,
        text=True,
    )

    stdout_lines = [line.strip() for line in fouine_result.stdout.splitlines() if line.strip() != ""]
    actual = stdout_lines[-1] if stdout_lines else ""

    ok = fouine_result.returncode == 0 and actual == expected

    if ok:
        cprint(f"Alpha test {file} passed", "green")
    else:
        cprint(f"Alpha error in {file}", "red")
        cprint(f"Expected : {expected}", "red")
        cprint(f"Actual : {actual}", "red")
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
    and "reduce" not in root.split(os.sep)
    and "alpha" not in root.split(os.sep)
]

should_fail_files = [
    os.path.join(root, f)
    for root, dirs, files in os.walk("tests")
    for f in files
    if f.endswith(".8pus") and "temp.8pus" not in f
    and "ShouldFail" in root.split(os.sep)
]

reduce_files = [
    os.path.join(root, "term.lam")
    for root, dirs, files in os.walk("tests/reduce")
    if "term.lam" in files
]

alpha_files = [
    os.path.join(root, f)
    for root, dirs, files in os.walk("tests/alpha")
    for f in files
    if f.endswith(".lam")
]

nb_test = len(ml_files) + len(should_fail_files) + len(reduce_files) + len(alpha_files)

total = 0
for file in ml_files:
    total += test_should_be_ok(file)
for file in should_fail_files:
    total += test_should_fail(file)
for file in reduce_files:
    total += test_reduce_should_be_ok(file)
for file in alpha_files:
    total += test_alpha_should_be_ok(file)

print()
if total == nb_test:
    cprint(f"All {total} test passed !!", "green")
else:
    cprint(f"Some tests didnt pass : ({total}/{nb_test} correct).", "red")
