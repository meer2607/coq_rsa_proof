# coq_rsa_proof
This simple repository proves the correctness of a basic [RSA cryptosystem](https://en.wikipedia.org/wiki/RSA_(cryptosystem)) with the help of [Coq Proof Assistance](https://coq.inria.fr/)

This project was a part of [CS-494 course](https://www.cs.uic.edu/~mansky/teaching/cs494sf/sp22/index.html) at UIC under Prof. William Mansky.

In a nutshell it sets out to prove that, given all the involved variables are correct, decrypting an encrypted message, leads back to the original message.

More specifically: <br>
> For all: message, p, q, n, λn. e, d, <br>
    If p != q, p and q are prime numbers, <br>
    n = p * q, and if e and d are chosen according to RSA spec, <br>
    Then decrypt(encrypt(message)) = message (mod n) <br>
