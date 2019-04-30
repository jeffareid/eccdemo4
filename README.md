# eccdemo4
Interactive Reed Solomon ECC demo program for GF(2^4)

User interface - the program displays a list of alphas and field polynomials
and prompts the user to select one. It then prompts if the user want to use
a self-reciprocal polynomial, and if not, it will prompt for the first
consecutive root, 1 or alpha. It then prompts for the number of parity
elements, then the number of data elements. It then goes into interactive
mode: "e" - enter data. "c" - change data (errors). "p" - enter erasures.
"z" - zero all data. "n" - encode. "f" - fix (correct). "q" - quit.
