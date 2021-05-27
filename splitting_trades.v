Require Import ZArith.
Require Import Zorder.
Require Import Lia.
Require Import QArith.
Require Import Lqa.
Require Import QArith_base.

Section S_trade.

Variables r_a r_b a_1 a_2 b_1 b_2 b_t k_1 k_2: Z.

Hypothesis gamma : (0 <= k_1 < k_2)%Z.

Notation "[ i ]" := (inject_Z i) : Q_scope.

Hypothesis r_a_pos : (0 < r_a)%Z.
Hypothesis r_b_pos : (0 < r_b)%Z.
Hypothesis a_1_pos : (0 < a_1)%Z.
Hypothesis a_2_pos : (0 < a_2)%Z.
Hypothesis b_1_pos : (0 < b_1)%Z.
Hypothesis b_2_pos : (0 < b_2)%Z.
Hypothesis b_t_pos : (0 < b_t)%Z.
Hypothesis r_b_1_gt : (b_1 < r_b)%Z.

Hypothesis constant_prod_1 : 
(([r_a] + [a_1] + ([k_1]/[k_2])*[a_2])* ([r_b] - [b_1] - [b_2]) == ([r_a] + [a_1])*([r_b] - [b_1]))%Q.

Hypothesis constant_prod_2 : 
(([r_a] + ([k_1]/[k_2])* ([a_1] + [a_2])) * ([r_b] - [b_t]) == [r_a] * [r_b])%Q.

Hypothesis constant_prod_3 :
(([r_a] + ([k_1]/[k_2])*[a_1]) * ([r_b] - [b_1]) == [r_a] * [r_b])%Q.

Lemma Qmult_pos : forall x y , (x > 0 -> y > 0 -> (x * y) > 0)%Q.
Proof.
Admitted.

Lemma minus_distr : forall a b c, (a - (b + c) == a - b -c)%Q.
Proof. intros. ring.
Admitted.

Ltac simplify_exp := try lra ; try omega ; try nra.

Lemma Qminus_lt_l : forall x y z , (x < y -> z - y < z - x)%Q.
Proof. Admitted.

Lemma Qmult_div_distr : forall x y z , ( z > 0 -> x * y / z == x / z * y)%Q.
Proof. intros. field. Admitted.

Lemma Qplus_gt_0 : forall x y z , ( x > 0 -> y > 0 -> z >= 0 -> x + y + z > 0)%Q.
Proof. intros. lra.
Qed.

Lemma Qplus_gt_0_2 : forall x y , ( x > 0 -> y >= 0 -> x + y > 0)%Q.
Proof. intros. lra.
Qed.

Lemma Qmult_gt_0 : forall x y z , ( x >= 0 -> y > 0 -> z > 0 -> x / y * z >= 0)%Q.
Proof. intros.
Admitted.

Lemma Qadd_const_gt : forall x y z, ( z > 0 -> (x + z)/ (y + z) > x/y)%Q.
Proof. Admitted.

Lemma Zgt_ge : forall x y , (x > y -> y <= x)%Z.
Proof. Admitted.

Lemma inject_Z_minus : forall x y , [x - y] = [x] - [y].
Proof. intros.
       change (x - y)%Z with (x + - y) %Z.
       rewrite -> inject_Z_plus. rewrite -> inject_Z_opp.
       change ([x] + - [y])%Q with ([x] - [y])%Q. reflexivity.
Qed.

Ltac rat_to_int_ineq := change 0 with [0] ;
                        try (rewrite <- inject_Z_minus); 
                        try (rewrite <- Zlt_Qlt);
                        try (rewrite <- Zle_Qle ); 
                        try (apply r_a_pos) ; try (apply r_b_pos);
                        try (apply a_1_pos) ; try (apply a_2_pos) ; try (apply b_1_pos) ; try (apply b_2_pos) ; 
                        try (apply b_t_pos) ; try (apply (Z.le_lt_trans 0 k_1 k_2)) ;
                        try (apply gamma).

Lemma val_b_t : ([b_t] == [r_b] - (([r_a] + ([k_1]/[k_2])*[a_1]) * ([r_b] - [b_1]))/([r_a] + ([k_1]/[k_2])* ([a_1] + [a_2]))%Q).
Proof. Admitted.

Lemma val_b_1_2 : ([b_1] + [b_2] == [r_b] - (([r_a] + [a_1])*([r_b] - [b_1])/ ([r_a] + [a_1] + ([k_1]/[k_2])*[a_2])))%Q.
Proof. Admitted.

Lemma split_trade_rat : ([0] < [b_t] - ([b_1] + [b_2]))%Q.
Proof. intros.
       rewrite -> val_b_t.
       rewrite -> val_b_1_2.
       remember ([r_b] -
       ([r_a] + [k_1] / [k_2] * [a_1]) * ([r_b] - [b_1]) /
       ([r_a] + [k_1] / [k_2] * ([a_1] + [a_2])))%Q as x_1.
       remember ([r_b] -
       ([r_a] + [a_1]) * ([r_b] - [b_1]) /
       ([r_a] + [a_1] + [k_1] / [k_2] * [a_2]))%Q as x_2.
        change (x_1 - x_2)%Q with (x_1 + - x_2)%Q.
       rewrite <- Qlt_minus_iff.
       subst.
       eapply Qminus_lt_l.
       repeat (rewrite -> Qmult_div_distr).
       eapply Qmult_lt_compat_r.
       + rat_to_int_ineq.
         apply Z.lt_0_sub.
         apply r_b_1_gt.
       + remember ([k_1]/[k_2])%Q as c_1 in |- *.
         setoid_replace [a_1]%Q with ((1 - c_1)*[a_1] + c_1*[a_1])%Q at 3 by ring.
         setoid_replace [a_1]%Q with ((1 - c_1)*[a_1] + c_1*[a_1])%Q at 5 by ring.
         setoid_replace ([r_a] + ((1 - c_1) * [a_1] + c_1 * [a_1]))%Q with 
         ([r_a] + c_1 * [a_1] + (1 - c_1) * [a_1])%Q by ring.
         setoid_replace ([r_a] + c_1 * [a_1] + (1 - c_1) * [a_1] + c_1 * [a_2])%Q
         with ([r_a] + c_1 * ([a_1] + [a_2]) + (1 - c_1) * [a_1])%Q by ring. 
         eapply Qadd_const_gt.
         apply Qmult_pos.
         ++ change (1 - c_1)%Q with (1 + - c_1)%Q.
            rewrite <- Qlt_minus_iff. subst.
         Search ( _ / _ < _)%Q.
            apply Qlt_shift_div_r.
        Search inject_Z.
            change 0 with [0].
            rewrite <- Zlt_Qlt.
        About Z.le_lt_trans.
       apply (Z.le_lt_trans 0 k_1 k_2).
       apply gamma. apply gamma.
       change 1 with [1].
       rewrite <- inject_Z_mult.
       rewrite <- Zlt_Qlt.
       replace (1 * k_2)%Z with k_2%Z by lia.
       apply gamma.
       ++ change 0 with [0].
          rewrite <- Zlt_Qlt.
          apply a_1_pos.
     + apply Qplus_gt_0. rat_to_int_ineq. 
       rat_to_int_ineq.
       apply Qmult_gt_0. rat_to_int_ineq.
       rat_to_int_ineq. rat_to_int_ineq.
     + apply Qplus_gt_0_2. rat_to_int_ineq.
       apply Qmult_gt_0. rat_to_int_ineq.
       rat_to_int_ineq. apply Qplus_gt_0_2.
       rat_to_int_ineq. rat_to_int_ineq.
       apply Zgt_ge. 
       Search ( _ > _)%Z.
       apply Z.lt_gt. apply a_2_pos.
Qed.

Lemma split_trade_int : (b_t - (b_1 + b_2) > 0)%Z.
Proof. Search inject_Z.
       About Zlt_Qlt.
       apply Z.lt_gt.
       rewrite -> Zlt_Qlt.
       rewrite -> inject_Z_minus.
       rewrite -> inject_Z_plus.
       apply split_trade_rat.
Qed.
      

End S_trade. 
