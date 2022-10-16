Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.Zpower.
From Coq Require Import BinNums.

Definition is_prime (n:nat) : Prop :=
  n <> 0 /\ n <> 1 /\
  forall k, n mod k = 0 -> k = 1 \/ k = n.

(*
https://en.wikipedia.org/wiki/RSA_(cryptosystem)#Key_generation

1. Pick 2 prime numbers P, Q
2. Compute n = p * q
3. Compute λn = lcm (p-1) (q-1)
*)

Definition validλn (λn n p q : nat ) : Prop :=
  n = p * q ->
  is_prime p -> is_prime q ->
  λn = (p-1) * (q-1).

(*
4. Choose an integer e, such that 1 < e < λn, and gcd(e, λ(n)) = 1 :
*)

Definition valid_e (e λn : nat) : Prop :=
  e > 1 /\ e<λn /\ gcd e λn = 1.

(*
5. Calculate d, such that
    d * e = 1 (mod λn)
*)

Definition valid_d (d e λn : nat) : Prop :=
  d> 1 /\
  ( d * e) mod λn = 1.

(*
6. Encypt:
    ciphertext = m ^ e modulo n
*)

Definition encrypt ( msg e n : nat ) : nat :=  (msg ^ e) mod n.

(* 7. Decrypt
    message  = cipher ^ d modulo n
*)

Definition decrypt ( cipher d n : nat ) : nat := (cipher ^ d ) mod n.

(* Helper Lemmas
    TODO: Prove them *)

Theorem eulers_theorem : forall a n λn p q: nat,
  validλn λn n p q->
  gcd a n = 1 -> ( a ^ λn) mod n = 1.
Proof.
  (* https://en.wikipedia.org/wiki/Euler%27s_theorem *)
Admitted.

Theorem chinese_remainder : forall x y p q : nat,
  gcd p q  = 1 -> x mod p = y mod p  -> x mod q = y mod q ->
  x mod ( p * q ) = y mod ( p * q ).
Proof.
  (* https://en.wikipedia.org/wiki/Chinese_remainder_theorem *)
Admitted.

Theorem fermats_little_theorem:  forall a p : nat,
  a ^ (p-1) mod p = 1.
Proof.
  (* https://en.wikipedia.org/wiki/Fermat%27s_little_theorem *)
Admitted.

Lemma mod_pow:  forall (a b m : nat),
  ((a mod m) ^ b ) mod m = (a ^ b) mod m.
Proof.
  (* Informal proof:
     a ^ b = a * a * a ... b times
     So, using the principle:
     (x * y) % m = ( x%m * y%m )%m
     (a ^ b)%m can be written as:
     ( a%m * a%m * a%m ... b times )%m
     Which is nothing but
     ((a%m)^ b ) mod m
  *)
Admitted.

Lemma mod_inv: forall (a b m : nat),
  a mod m = b -> (b<m) -> exists k :nat, a = b + m * k.
Proof.
  Search "mod_unique".
  intros a b m Habm Hbm.
  exists 1. rewrite add_comm. Search "mod_unique".
  Fail rewrite mod_unique with (a:=a) (b:=m) (r:=b) (q:=1).
Admitted.

Lemma mult_not_0 : forall (a b : nat),
  ( a * b ) <> 0 <-> a <> 0 /\ b <> 0.
Proof. lia. Qed.

Lemma prime_gcd : forall (p q : nat ),
  is_prime p -> is_prime q -> gcd p q = 1.
Proof. Admitted.

Lemma gcd_prime_factors : forall (m p q : nat),
  m <> (p*q) ->
  gcd m (p*q) <> 1 ->
  is_prime p -> is_prime q ->
  gcd m (p*q) = p \/ gcd m (p*q) = q.
Proof.
  (*
  GCD (m n), where n is the product of two
  primes p and q.
  If (gcd m n) != 1, then m and n must have common factors.
  The only two factors n has are p and q
  So, when m != n,
  gcd m n must be either p or q.
 *)
Admitted.

Lemma gcd_mod : forall (a b f : nat),
  gcd a b = f ->
  a mod f = 0 /\ b mod f = 0.
Proof.
  (* f is a factor of both a and b *)
Admitted.

Lemma gcd_neq_0_r : forall (a b : nat),
  gcd a b <> a -> b <> 0.
(* If one of them is 0, then gcd is the other *)
Proof. Admitted.

Lemma gcd_neq_0_l : forall (a b : nat),
  gcd a b <> b -> a <> 0.
Proof. Admitted.

Lemma mul_neq_r: forall (a b : nat),
  a <> 1 -> b<>0 -> b <> (a*b).
Proof. Admitted.

Lemma mul_neq_l : forall (a b : nat),
  b <> 1 -> a<>0 -> a <> (a*b) .
Proof. Admitted.

Lemma pow_minus_1 : forall (a exp : nat),
  a <> 0 -> exp >= 1 -> a ^ exp = a ^ (exp - 1) * a.
Proof.
intros.
   rewrite pow_sub_r. rewrite pow_1_r.
   rewrite mul_comm. rewrite <- divide_div_mul_exact.
   rewrite mul_comm. rewrite div_mul. reflexivity.
   - assumption.
   - assumption.
   - (* Is obvious but it requires this very theorem *)
     admit.
   - assumption.
   - assumption.
Admitted.

Lemma mult_ge_1 : forall (n1 n2 : nat),
  n1 >= 1 -> n2>=1 -> n1 * n2>=1.
lia. Qed.

(* For concisness *)
Lemma prime_neq_0 : forall (p: nat),
  is_prime p -> p<>0.
  intros p Hp.
  unfold is_prime in Hp.
  destruct Hp  as [Hp0 Hp]. auto.
Qed.

Lemma prime_neq_1 : forall (p: nat),
  is_prime p -> p<>1.
  intros p Hp.
  unfold is_prime in Hp.
  destruct Hp  as [Hp0 [Hp1 Hp]]. auto.
Qed.

(* Main Proof:
    Pen and paper version referred from :
    https://crypto.stackexchange.com/a/2894
*)

Theorem rsa_proof :
  forall msg p q n λn e d : nat,
  p <> q ->
  ( is_prime p ) -> ( is_prime q ) ->
  n = p * q ->  validλn λn n p q->
  ( valid_e e λn ) -> ( valid_d d e λn )->
  decrypt ( encrypt msg e n ) d n = msg mod n.
Proof.
  intros msg p q n λn e d.
  intros Hpq Hprimep Hprimeq Hn Hλn He Hd.
  (* Getting all the hypotheses *)
  inversion He. clear He. rename H into He1.
  destruct H0 as [ He2 He3 ].
  inversion Hd. clear Hd. rename H0 into Hd1.
  unfold encrypt. unfold decrypt.
  destruct ( gcd msg ( p * q ) =? 1) eqn: H_gcd_n_msg.
  { (* Euler's theorem holds *)
     rewrite mod_pow.
     rewrite <- pow_mul_r.
     apply mod_inv in Hd1. rewrite mul_comm.
     destruct Hd1 as [k Hd1].
     rewrite Hd1. rewrite pow_add_r.
     rewrite pow_1_r. rewrite pow_mul_r.
     rewrite <- mul_mod_idemp_r. rewrite <- mod_pow.
     rewrite eulers_theorem with (a:=msg)(p:=p)(q:=q).
     rewrite mul_mod_idemp_r. rewrite pow_1_l.
     rewrite mul_1_r. reflexivity. (* WOW! *)
     - rewrite Hn.
       apply mult_not_0. split; try apply prime_neq_0; try auto.
     - auto.
     - apply Nat.eqb_eq. rewrite Hn. apply H_gcd_n_msg.
     - rewrite Hn.
       apply mult_not_0. split; try apply prime_neq_0; try auto.
     - apply lt_trans with (m:=e); auto.
  }
  {
    rewrite mod_pow.
    rewrite Hn.
    rewrite <- chinese_remainder with (x:=((msg ^ e) ^ d) ) (y:=msg);
    try auto.
    - apply prime_gcd; auto.
    - apply beq_nat_false in H_gcd_n_msg.
      apply gcd_prime_factors in H_gcd_n_msg; auto.
      destruct H_gcd_n_msg.
      + rewrite <- mod_pow. rewrite <- mod_pow with (a:=msg) (b:=e).
          apply gcd_mod in H0. destruct H0 as [Hmp Hnp].
          rewrite Hmp. rewrite pow_0_l. rewrite mod_0_l.
          rewrite pow_0_l. rewrite mod_0_l. reflexivity.
          * try apply prime_neq_0; try auto.
          * lia.
          * try apply prime_neq_0; try auto.
          * lia.
      + rewrite <- pow_mul_r.
          rewrite pow_minus_1.
          * assert (Hed: exists h:nat, (e*d) = (h * (p-1) * (q-1))+1).
            { apply mod_inv in Hd1; try auto.
               - destruct Hd1 as [k Hd1]. exists k.
                 rewrite  <- mul_assoc.
                 unfold validλn in Hλn.
                 rewrite <- Hλn; try auto. rewrite mul_comm.
                 rewrite add_comm. rewrite mul_comm with (n:=k).
                 auto.
               - unfold validλn in Hλn.
                 rewrite Hλn; auto.
                 (* P and Q are unique primes, so the least possible
                     values  are 2 and 3. *)
                 admit.
             }
             destruct Hed as [h Hed].
             rewrite Hed. rewrite add_sub.
             rewrite mul_comm with (n:=(h * (p - 1))).
             rewrite mul_assoc.
             rewrite mul_comm with (m:= (p - 1)).
             rewrite pow_mul_r.
             rewrite <- mul_mod_idemp_l.
             rewrite <- mod_pow.
             rewrite fermats_little_theorem.
             rewrite pow_1_l.
             rewrite mul_mod_idemp_l.
             simpl. rewrite <- plus_n_O. reflexivity. (* WOHOO *)
             ** try apply prime_neq_0; try auto.
             **  try apply prime_neq_0; try auto.
          * apply gcd_neq_0_l with (b:=(p*q)).
               rewrite H0. apply mul_neq_r.
               **   apply prime_neq_1. try auto.
               **   try apply prime_neq_0; try auto.
          * apply mult_ge_1; lia.
       + (* I cannot understand, why any proof I encountered did
              not come across this case, but this cannot be proved
              in the current state *) admit.
    - apply beq_nat_false in H_gcd_n_msg.
      apply gcd_prime_factors in H_gcd_n_msg; auto.
      destruct H_gcd_n_msg.
      + rewrite <- pow_mul_r.
          rewrite pow_minus_1.
          * assert (Hed: exists h:nat, (e*d) = (h * (p-1) * (q-1))+1).
            { apply mod_inv in Hd1; try auto.
               - destruct Hd1 as [k Hd1]. exists k.
                 rewrite  <- mul_assoc.
                 unfold validλn in Hλn.
                 rewrite <- Hλn; try auto. rewrite mul_comm.
                 rewrite add_comm. rewrite mul_comm with (n:=k).
                 auto.
               - unfold validλn in Hλn.
                 rewrite Hλn; try auto.
                 (* P and Q are unique primes, so the least possible
                     values  are 2 and 3. *)
                 admit.
             }
             destruct Hed as [h Hed].
             rewrite Hed. rewrite add_sub.
             rewrite mul_comm with (n:=(h * (p - 1))).
             rewrite pow_mul_r.
             rewrite <- mul_mod_idemp_l.
             rewrite <- mod_pow.
             rewrite fermats_little_theorem.
             rewrite pow_1_l.
             rewrite mul_mod_idemp_l.
             simpl. rewrite <- plus_n_O. reflexivity. (* WOHOO *)
             ** unfold is_prime in Hprimeq.
                 destruct Hprimeq  as [Hp0 Hprimeq]. auto.
             ** unfold is_prime in Hprimeq.
                 destruct Hprimeq  as [Hp0 Hprimeq]. auto.
          * apply gcd_neq_0_l with (b:=(p*q)).
               rewrite H0. apply mul_neq_l.
               **  unfold is_prime in Hprimeq.
                    destruct Hprimeq  as [Hp0 [Hp1 Hprime1]]. auto.
               ** unfold is_prime in Hprimep.
                  destruct Hprimep  as [Hp0 Hprimep]. auto.
          * apply mult_ge_1; lia.
      + rewrite <- mod_pow. rewrite <- mod_pow with (a:=msg) (b:=e).
          apply gcd_mod in H0. destruct H0 as [Hmp Hnp].
          rewrite Hmp. rewrite pow_0_l. rewrite mod_0_l.
          rewrite pow_0_l. rewrite mod_0_l. reflexivity.
          * unfold is_prime in Hprimeq.
             destruct Hprimeq  as [Hp0 Hprimeq]. auto.
          * lia.
          * unfold is_prime in Hprimeq.
             destruct Hprimeq  as [Hp0 Hprimeq]. auto.
          * lia.
      + admit. (* TODO: Figure out why this case is not possible *)
  }
Admitted.
