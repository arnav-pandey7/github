#  Legendre's Conjecture and Lean 4 for it:

I have a minimalist, dependency-free **Lean 4** project exploring **Legendre's Conjecture**. I am a 15-year-old student passionate about math and astronomy, and I built this to share my knowledge and proof with formal verification.

## What is Legendre's Conjecture:
Legendre's conjecture is a famous, unsolved problem in number theory. It states that for every positive integer $n$, there is always at least one prime number between $n^2$ and $(n+1)^2$.

For example:
* If $n = 4$
* $4^2 = 16$ and $5^2 = 25$
* The prime numbers inside this gap are **17, 19, 23**.

This repository uses the **Lean 4 Interactive Theorem Prover** to write clean, logical code around this mathematical problem.


From the lean codes, I have defined the prime numbers as the numbers remaining or surviving the sieve process(given), from $p^2$, where p is a prime number and up to another prime number square. Then I have compared with the natural number $n >= p $


I am always looking to learn and improve my code. If you find a better way to structure a tactic, see a logic bug, or want to suggest improvements, please help me.


