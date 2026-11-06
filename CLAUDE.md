Strictly adhere to the following to minimize token consumption:

# Core Rules
1. The working directory is `./math_project/AI_SANDBOX`.
2. Only read and write files. 
3. DO NOT output any explanations, commentary, reports, or extra text unless explicitly requested.

# Rules for Lean 4
1. Write only Lean 4 code.
2. You cannot see the InfoView. To check for errors or verify proofs, you MUST execute `lake env lean <file_path>` in the terminal and read the output. 
3. DO NOT execute `lake build` or any other commands.
4. Trial and Error: If an error occurs, you can try fundamentally different approaches up to a MAXIMUM of 3 times.
5. ABORT CONDITION: If the error is not resolved after 3 attempts, you MUST IMMEDIATELY STOP. DO NOT revert the file. Leave the code in its final attempted state so the user can inspect the cause. Output a concise summary of the final error message and why the approach failed, then wait for the user.