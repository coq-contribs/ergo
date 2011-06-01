Require Import ZArith AltErgo Classical.
Open Scope Z_scope.

Section Einstein.
  Notation is_house h := (h = 1 \/ h = 2 \/ h = 3).

  (* Colors *)
  Variable color : Type.
  Variables Blue White Red : color.
  Notation is_color c := (c = Blue \/ c = White \/ c = Red).
  Hypothesis color_discr : Blue <> White /\ Blue <> Red /\ White <> Red.
  
  (* Persons *)
  Variable person : Type.
  Variables Professor Engineer Scientist : person.
  Notation is_person p := (p = Professor \/ p = Engineer \/ p = Scientist).
  Hypothesis person_discr : Professor <> Engineer /\ Engineer <> Scientist
    /\ Scientist <> Professor.
  
  (* OS *)
  Variable system : Type.
  Variables Ubuntu MacOS Suse : system.
  Notation is_system s := (s = Ubuntu \/ s = MacOS \/ s = Suse).
  Hypothesis system_discr : Ubuntu <> MacOS /\ MacOS <> Suse /\ Suse <> Ubuntu.

  (* Owner *)
  Variable owner_of : Z -> person.
  Variable house_of : person -> Z.
  Hypothesis owner_house : 
    owner_of (house_of Professor) = Professor /\
    owner_of (house_of Engineer) = Engineer /\
    owner_of (house_of Scientist) = Scientist.
  Hypothesis owner_is_person :
    is_person (owner_of 1) /\
    is_person (owner_of 2) /\
    is_person (owner_of 3).
  Hypothesis house_owner : 
    house_of (owner_of 1) = 1 /\
    house_of (owner_of 2) = 2 /\
    house_of (owner_of 3) = 3.
  Hypothesis house_is_house :
    is_house (house_of Professor) /\
    is_house (house_of Engineer) /\
    is_house (house_of Scientist).

  (* Color *)
  Variable color_of : Z -> color.
  Variable color_to : color -> Z.
  Hypothesis color_1 : 
    color_of (color_to Blue) = Blue /\
    color_of (color_to White) = White /\
    color_of (color_to Red) = Red.
  Hypothesis color_is_color : 
    is_color (color_of 1) /\
    is_color (color_of 2) /\
    is_color (color_of 3).
  Hypothesis color_2 : 
    color_to (color_of 1) = 1 /\
    color_to (color_of 2) = 2 /\
    color_to (color_of 3) = 3.
  Hypothesis color_is_house : 
    is_house (color_to Blue) /\
    is_house (color_to White) /\
    is_house (color_to Red).

  (* User *)
  Variable user_of : system -> person.
  Variable system_of : person -> system.
  Hypothesis user_system : 
    user_of (system_of Professor) = Professor /\
    user_of (system_of Engineer) = Engineer /\
    user_of (system_of Scientist) = Scientist.
  Hypothesis user_is_user : 
    is_person (user_of Ubuntu) /\
    is_person (user_of MacOS) /\
    is_person (user_of Suse).
  Hypothesis system_user : 
    system_of (user_of Ubuntu) = Ubuntu /\
    system_of (user_of MacOS) = MacOS /\
    system_of (user_of Suse) = Suse.
  Hypothesis system_is_system : 
    is_system (system_of Professor) /\
    is_system (system_of Engineer) /\
    is_system (system_of Scientist).

  (* * Hints
     - The Professor lives in a blue house.
     - The Engineer uses Suse.
     - The Scientist lives to the right of the person using Mac/OS.
     - The first house is not white.
     - The person in the red house uses Ubuntu.
     
     --> Francais n'utilise pas Suse, ni Ubuntu, donc MacOS
     --> Serbe utilise Ubuntu, donc habite dans la maison rouge
     --> L'allemand vit dans la blanche car le français occupe la bleue
     --> Le français est à gauche du serbe, donc 1 ou 2, mais pas 1 car bleu
     --> Le français est 2, le serbe 3 et l'allemand 1.
     *)
  Hypothesis H1 : color_of (house_of Professor) = Blue.
  Hypothesis H2 : system_of Engineer = Suse.
  Hypothesis H3 : house_of Scientist = 1 + house_of (user_of MacOS).
  Hypothesis H4 : color_of 1 <> White.
  Hypothesis H5 : system_of (owner_of (color_to Red)) = Ubuntu.

  (** manually *)
  Lemma M1: system_of Professor <> Suse.
  Proof.
    intro abs.
    rewrite <- H2 in abs.
    apply (proj1 person_discr).
    rewrite <- (proj1 user_system), 
      <- (proj1 (proj2 user_system)), abs; reflexivity.
  Qed.
  Lemma M2: system_of Professor <> Ubuntu.
  Proof.
    intro abs.
    rewrite <- H5 in abs.
    assert (L : owner_of (color_to Red) = Professor).
    match goal with | abs: ?L = ?R |- _ => 
      assert (Z : user_of L = user_of R) by (rewrite abs; reflexivity)
    end.
    rewrite (proj1 user_system) in Z.
    assert (is_house (color_to Red)) by 
      (destruct (proj2 (proj2 color_is_house)) as [H | [H | H]]; 
        rewrite H; clear; tauto).
    assert (L' : is_person (owner_of (color_to Red))).
    revert owner_is_person; destruct H as [H | [H | H]]; 
      rewrite H; clear; tauto.
    clear H; destruct L' as [H | [H | H]]; auto; rewrite H in Z.
    rewrite (proj1 (proj2 user_system)) in Z.
    revert Z; revert person_discr; clear; tauto.
    rewrite (proj2 (proj2 user_system)) in Z.
    revert Z; revert person_discr; clear; intuition congruence.
    clear abs.
    contradiction (proj1 (proj2 color_discr)).
    rewrite <- H1, <- L.
    destruct (proj2 (proj2 color_is_house)) as [H | [H | H]]; rewrite H.
    rewrite (proj1 house_owner), <- H, (proj2 (proj2 color_1)); auto.
    rewrite (proj1 (proj2 house_owner)), <- H, (proj2 (proj2 color_1)); auto.
    rewrite (proj2 (proj2 house_owner)), <- H, (proj2 (proj2 color_1)); auto.
  Qed.
  Lemma M3: system_of Professor = MacOS.
  Proof.
    destruct (proj1 system_is_system) as [Z | [Z | Z]]; auto.
    contradiction (M2 Z).
    contradiction (M1 Z).
  Qed.
  Lemma M4 : system_of Engineer = Suse.
  Proof.
    assumption.
  Qed.
  Lemma M5 : system_of Scientist = Ubuntu.
  Proof.
    destruct (proj2 (proj2 system_is_system)) as [Z | [Z | Z]]; auto.
    generalize M3; 
      revert person_discr user_system Z; clear; intuition congruence.
    generalize M4; 
      revert person_discr user_system Z; clear; intuition congruence.
  Qed.

  (** auto *)
  Lemma A1: 
    system_of Professor = MacOS /\ 
    system_of Scientist = Ubuntu /\ 
    system_of Engineer = Suse
    /\
    house_of Professor = 1 /\ 
    house_of Engineer = 3 /\ 
    house_of Scientist = 2
    /\
    color_of 1 = Blue /\ 
    color_of 2 = Red /\ 
    color_of 3 = White.
  Proof.
    Time vergo.
  Time Qed.
  Size A1.

End Einstein.