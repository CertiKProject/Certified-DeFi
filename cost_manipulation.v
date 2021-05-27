From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Reals.

Open Scope R_scope.

Variable eps : R.

Definition f (x : R) := x + (1 / x).

Definition kappa := (3/2) - (sqrt 2).

Lemma aux_f_kappa_ineq : forall (x : R) ,
 (x >= 1 -> f x - 2 >= kappa * x )%R.
Proof. intros. 