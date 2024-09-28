Require Setoid.

Module MyNat.
    Inductive myNat :=
        O | S (n:myNat).

    Local Notation "0" := O.
    Local Notation "1" := (S O).
    Local Notation "2" := (S (S O)).
    Local Notation "3" := (S (S (S O))).
    Local Notation "4" := (S (S (S (S O)))).
    Local Notation "5" := (S (S (S (S (S O))))).
    Local Notation "6" := (S (S (S (S (S (S O)))))).
    Local Notation "7" := (S (S (S (S (S (S (S O))))))).
    Local Notation "8" := (S (S (S (S (S (S (S (S O)))))))).
    Local Notation "9" := (S (S (S (S (S (S (S (S (S O))))))))).
    Local Notation "10" := (S (S (S (S (S (S (S (S (S (S O)))))))))).

    Create HintDb myNatDB.

    Fixpoint add (a: myNat) (b: myNat) :=
        match b with
            | O => a
            | S b' => S (add a b')
        end.

    Notation "x + y" := (add x y) (at level 50, left associativity).

    Fixpoint mul (a: myNat) (b: myNat) :=
        match b with
            | O => O
            | S b' => a + mul a b'
        end.

    Notation "x * y" := (mul x y) (at level 40, left associativity).

    Lemma addZero: forall n: myNat, n + O = n.
    Proof.
        compute.
        reflexivity.
    Qed.

    Lemma zeroAdd: forall n: myNat, O + n = n.
    Proof.
        induction n.
        - trivial.
        - simpl. rewrite IHn. reflexivity.
    Qed.


    Lemma addingIntoS: forall n m: myNat, S n + m = S (n + m).
    Proof.
        intros n m.
        induction m.
        - simpl. reflexivity.
        - simpl. rewrite IHm. reflexivity.
    Qed. 


    Lemma addCommutative: forall n m: myNat, n + m = m + n.
    Proof.
        induction m.
        - simpl. rewrite zeroAdd. reflexivity.
        - simpl. rewrite addingIntoS. rewrite IHm. reflexivity.
    Qed.


    Lemma addInjective: forall n m o: myNat, n + m = n + o -> m = o.
    Proof.
        intros n m o H.
        induction n.
        - repeat rewrite zeroAdd in H. exact H.
        - apply IHn. 
        repeat rewrite addingIntoS in H.
        injection H. intros A. apply A.
    Qed.


    Lemma addAssociative: forall n m o: myNat, n + (m + o) = (n + m) + o.
    Proof.
        intros n m o.
        induction n.
        - simpl. repeat rewrite zeroAdd. reflexivity.
        - simpl. repeat rewrite addingIntoS.
        f_equal. apply IHn.
    Qed.

    
    Hint Resolve addZero zeroAdd addingIntoS addCommutative addInjective addAssociative : myNatDB.
    Hint Rewrite addZero zeroAdd addingIntoS addCommutative addInjective addAssociative : myNatDB.


    Lemma mulZero: forall n : myNat, n * 0 = 0.
    Proof.
        compute.
        reflexivity.
    Qed.

    Lemma zeroMul: forall n : myNat, 0 * n = 0.
    Proof.
        intros n.
        induction n.
        - simpl. reflexivity.
        - simpl. rewrite zeroAdd. apply IHn.
    Qed.

    Lemma mulOne: forall n : myNat, n * 1 = n.
    Proof.
        compute.
        reflexivity.
    Qed.

    Lemma OneMul: forall n: myNat, 1 * n = n.
    Proof.
        intros n.
        induction n.
        - simpl. reflexivity.
        - simpl. rewrite IHn. rewrite addCommutative. simpl. reflexivity.
    Qed.


    Lemma multIntoS0: forall n m: myNat, n * S m = n + n * m.
    Proof.
        simpl.
        reflexivity.
    Qed.


    Lemma multIntoS: forall n m: myNat, S n * m = n * m + m.
    Proof.
        induction m.
        - simpl. reflexivity.
        - simpl. rewrite addingIntoS. f_equal.
        rewrite <- addAssociative. f_equal. apply IHm.
    Qed. 


    Lemma dist: forall n m p: myNat, (m + p) * n = m * n + p * n.
    Proof.
        intros n m p.
        induction n.
        - simpl. reflexivity. 
        - simpl. rewrite <- addAssociative. rewrite <- addAssociative.
            f_equal. rewrite addAssociative.
            rewrite addCommutative with (m * n) p.
            rewrite <- addAssociative with p (m * n) (p * n).
            f_equal.
            apply IHn.
    Qed.
        

    Lemma multCommutative: forall n m: myNat, n * m = m * n.
    Proof.
        intros n m.
        induction m.
        - simpl. rewrite zeroMul. reflexivity.
        - simpl. rewrite IHm. rewrite multIntoS. rewrite addCommutative.
            reflexivity. 
    Qed.

    Lemma multAssociative: forall n m o: myNat, n * (m * o) = (n * m) * o.
    Proof.
        intros n m p.
        induction n.
        - repeat rewrite zeroMul. reflexivity.
        - rewrite multIntoS. rewrite IHn. rewrite multIntoS.
            rewrite dist. reflexivity.
    Qed.

    Fixpoint sumDownFromN (a: myNat) :=
        match a with
            | O => O
            | S a' => a + sumDownFromN a'
        end.


    Lemma gaussianSum: forall n: myNat, 2 * sumDownFromN n = n * (n + 1).
    Proof.
        intros n.
        induction n.
        - compute. reflexivity.
        - rewrite multCommutative. simpl.
          rewrite addAssociative. 
          rewrite <- addAssociative with (S n) (sumDownFromN n) (S n).
          rewrite addCommutative with (sumDownFromN n) (S n).
          rewrite addAssociative.
          rewrite addAssociative.
          simpl.
          rewrite <- addAssociative.
          f_equal.
          rewrite multCommutative in IHn. simpl in IHn.
          rewrite multCommutative. simpl.
          apply IHn.
    Qed.


    Fixpoint pow (a: myNat) (b: myNat) :=
        match b with
            | O => 1
            | S b' => a * (pow a b')
        end.

    Lemma zeroPower: forall n : myNat, (n = O /\ pow 0 n = 1) \/ (n <> 0 /\ pow 0 n = 0).
    Proof.
        destruct n.
            + compute. left. split. reflexivity. reflexivity.
            + right. split. discriminate.
            simpl. apply zeroMul.
    Qed.

    Lemma onePower: forall n : myNat, pow 1 n = 1.
    Proof.
        induction n.
        - compute. reflexivity.
        - simpl. rewrite OneMul. apply IHn.
    Qed.

    Fixpoint powerSumDownFromN (a: myNat) (p: myNat) :=
    match a with
        | O => O
        | S a' => pow a p + powerSumDownFromN a' p
    end.

    Lemma powerGaussianSum: forall n: myNat, 6 * powerSumDownFromN n 2 = n * (n + 1) * (2 * n + 1).
    Proof.
        induction n.
        - compute. reflexivity.
        - simpl.
        rewrite addCommutative with (S n) (S n * n).
        rewrite multCommutative with (S n) n.
        rewrite <- multIntoS. 
        replace 2 with (1 + 1) at 3.
        rewrite <- addAssociative with 1 1 (2 * n).
        rewrite addCommutative with 1 (2 * n).
        rewrite multCommutative with (S n + S n * S n) (1 + (2 * n + 1)).
        rewrite dist.
        rewrite OneMul.
        rewrite addAssociative.
        replace (S n) with (n + 1) at 10.
        rewrite dist with (S n) n 1.
        rewrite OneMul.
        rewrite addCommutative with (n * S n) (S n).
        rewrite addAssociative with (S n) (S n) (n * S n).
        rewrite multCommutative with (2 * n + 1) (S n + S n + n * S n).
        rewrite dist with (2 * n + 1) (S n + S n) (n * S n).
        replace (S n + S n) with (n + n + 2).
        rewrite addAssociative.
        replace (S n) with (n + 1) at 9.
        rewrite <- IHn.
        simpl.
        rewrite addAssociative with (S n) (S n) (S n * n).
        rewrite <- addAssociative with (S n + S n) (S n * n) (S n + S n + S n * n).
        rewrite addCommutative with (S n * n) (S n + S n + S n * n).
        rewrite <- addAssociative with (S n + S n) (S n * n) (S n * n).
        rewrite addAssociative with (S n + S n) (S n + S n) (S n * n + S n * n).
        rewrite addAssociative with (S n + S n + (S n + S n) + (S n * n + S n * n)) (S (S (n + n))) (S (S (n + n)) * (2 * n)).
        rewrite <- addAssociative with (S n + S n + (S n + S n)) (S n * n + S n * n) (S (S (n + n))).
        rewrite addCommutative with (S n * n + S n * n) (S (S (n + n))).
        rewrite addAssociative with (S n + S n + (S n + S n)) (S (S (n + n))) (S n * n + S n * n).
        replace (S (S (n + n))) with (S n + S n). 
        replace (S n + S n) with (2 * (S n)).
        rewrite <- dist.
        rewrite <- dist.
        replace (2 + 2 + 2) with 6.
        replace (S n * n + S n * n) with (2 * (S n * n)).
        rewrite multAssociative with (2 * S n) 2 n.
        rewrite <- multAssociative with 2 (S n) 2.
        rewrite multCommutative with (S n) 2.
        rewrite multAssociative with 2 2 (S n).
        rewrite <- multAssociative with (2 * 2) (S n) n.
        rewrite <- addAssociative with (6 * S n) (2 * (S n * n)) (2 * 2 * (S n * n)).
        rewrite <- dist with (S n * n) 2 (2 * 2).
        replace (2 + 2 * 2) with 6.
        rewrite multCommutative.
        rewrite <- addAssociative with (S n) (S n * n) (powerSumDownFromN n 2).
        rewrite dist.
        rewrite dist with 6 (S n * n) (powerSumDownFromN n 2).
        rewrite addAssociative.
        rewrite multCommutative with 6 (S n).
        rewrite multCommutative with 6 (S n * n).
        rewrite multCommutative with 6 (powerSumDownFromN n 2).
        reflexivity.

        trivial.

        replace 2 with (1 + 1). 
        rewrite dist.
        rewrite OneMul.
        reflexivity.

        trivial.

        trivial.

        replace 2 with (1 + 1). 
        rewrite dist.
        rewrite OneMul.
        reflexivity.

        trivial.

        rewrite addingIntoS.
        rewrite addCommutative.
        rewrite addingIntoS.
        reflexivity.

        simpl.
        reflexivity.

        replace 2 with (1 + 1).
        rewrite addAssociative with (n + n) 1 1.
        rewrite <- addAssociative with n n 1.
        rewrite <- addAssociative with n (n + 1) 1.
        rewrite addCommutative with (n + 1) 1.
        rewrite addAssociative.
        simpl.
        reflexivity.

        trivial.

        trivial.

        trivial.
    Qed.

End MyNat.

Export MyNat.

