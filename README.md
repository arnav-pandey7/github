#  Legendre's Conjecture and Lean 4 for it:

I have a minimalist, dependency-free **Lean 4** project exploring **Legendre's Conjecture**. I am a 15-year-old student passionate about math and astronomy, and I built this to share my knowledge and proof with formal verification.

## What is Legendre's Conjecture:
Legendre's conjecture is a famous, unsolved problem in number theory. It states that for every positive integer $n$, there is always at least one prime number between $n^2$ and $(n+1)^2$.

For example:
* If $n = 4$
* $4^2 = 16$ and $5^2 = 25$
* The prime numbers inside this gap are **17, 19, 23**.

This repository uses the **Lean 4 Interactive Theorem Prover** to write clean, logical code around this mathematical problem.

To read and verify the code, you will need the Lean 4 toolchain installed. You can set it up quickly by running this in your terminal:

```bash
curl https://githubusercontent.com -sSf | sh
```

### 2. Installation
Clone the repository and move into the project directory:

```bash
git clone https://github.com
cd YOUR_REPO_NAME
```

### 3. Verification
To check the logic and compile the file, run:

```bash
lake build
```
*If it runs and finishes with zero errors, the logic successfully compiles!*

---

## Repository Structure
To keep the code as lean as possible, the project uses a single-file approach:
* `Main.lean` — The core file containing all definitions, mathematical assumptions, and proof steps.
* `lakefile.lean` — The configuration file for the Lean package manager.

I am always looking to learn and improve my code. If you find a better way to structure a tactic, see a logic bug, or want to suggest improvements, please help me.

## License
This project is open-source and available under the **MIT License**.

