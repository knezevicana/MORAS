Set Implicit Arguments.
Require Import Setoid.
Require Import Bool.

(* 1 a *)

Goal forall x y,
  negb (x && y) || (negb x && y) || (negb x && negb y) = (negb x || negb y).
Proof.
  intros x y.
  destruct x, y;
  simpl;
  reflexivity.

Qed.

(* 1 b *)
Goal forall(x y z : bool), 
  andb (andb (negb( andb (andb (negb x) (y)) (negb z))) 
  (negb(andb (andb(x) (y)) (z))) ) ( andb (andb (x) (negb y)) (negb z) ) = andb (andb (x) (negb y)) (negb z). 
Proof.
  intros x  y z.
  destruct x, y, z ;
  simpl;
  reflexivity.

Qed.
