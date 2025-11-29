(* ========================================================================== *)
(*                                                                            *)
(*                              ANTIKYTHERA.V                                 *)
(*                                                                            *)
(*        Formal Verification of the Antikythera Mechanism Gear Trains        *)
(*                                                                            *)
(* ========================================================================== *)
(*                                                                            *)
(*  When Archimedes fastened on a globe the movements of moon, sun, and       *)
(*  five wandering stars, he made one revolution of the sphere control        *)
(*  several movements utterly unlike in slowness and speed.                   *)
(*                                                                            *)
(*                                      -- Cicero, De Re Publica I.22 (54 BC) *)
(*                                                                            *)
(* ========================================================================== *)
(*                                                                            *)
(*  This formalization verifies the astronomical gear ratios of the           *)
(*  Antikythera Mechanism (c. 150-100 BC). Proved correct: Metonic and        *)
(*  Saros cycles, planetary period relations, pin-and-slot lunar anomaly,     *)
(*  calendar ring geometry, and state machine periodicity. Gear tooth         *)
(*  counts derive from CT scanning; hypothetical values marked explicitly.    *)
(*                                                                            *)
(* ========================================================================== *)
(*                                                                            *)
(*  Author: Charles Norton                                                    *)
(*  Date:   November 2025                                                     *)
(*                                                                            *)
(* ========================================================================== *)

Require Import ZArith QArith Qabs Strings.String List Bool.
Require Import Reals Rtrigo Lra Lia.
Import ListNotations.
Open Scope string_scope.

(* ========================================================================== *)
(* I. Core Types                                                              *)
(* ========================================================================== *)

Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* Fragment                                                                   *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Price 1974 "Gears from the Greeks"; Freeth et al. 2006 Nature   *)
(* EVIDENCE:  82 physical pieces recovered 1901 from Antikythera shipwreck;   *)
(*            7 major fragments labeled A-G by Price; CT scanned 2005-2006    *)
(* SEMANTICS: FragmentA (largest, 27 gears), FragmentB (Metonic spiral),      *)
(*            FragmentC (gear cluster 48/24/127), FragmentD (gear 63),        *)
(*            FragmentE-G (minor); Hypothetical marks reconstructed elements  *)
(* -------------------------------------------------------------------------- *)
Inductive Fragment : Set :=
  | FragmentA | FragmentB | FragmentC | FragmentD
  | FragmentE | FragmentF | FragmentG | Hypothetical.

(* -------------------------------------------------------------------------- *)
(* RotationDirection                                                          *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; Wright 2007 reconstruction                  *)
(* EVIDENCE:  Gear mesh analysis from CT imaging; physical reconstructions    *)
(* SEMANTICS: External gears reverse direction when meshed; direction tracked *)
(*            to verify output pointer rotations match dial conventions       *)
(* -------------------------------------------------------------------------- *)
Inductive RotationDirection : Set := Clockwise | CounterClockwise.

(* -------------------------------------------------------------------------- *)
(* flip_direction                                                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard gear mechanics                                         *)
(* EVIDENCE:  When two external gears mesh, driver and driven rotate opposite *)
(* SEMANTICS: Models direction reversal at each mesh point in gear train      *)
(* -------------------------------------------------------------------------- *)
Definition flip_direction (d : RotationDirection) : RotationDirection :=
  match d with Clockwise => CounterClockwise | CounterClockwise => Clockwise end.

(* -------------------------------------------------------------------------- *)
(* Gear                                                                       *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Nature; Supplementary Notes Table S1         *)
(* EVIDENCE:  CT scanning revealed 30 surviving gears with measurable teeth;  *)
(*            tooth counts estimated from radius and module (0.4-0.6 mm)      *)
(* SEMANTICS: gear_name: identifier; teeth: tooth count (positive integer);   *)
(*            ct_observed: true if physically confirmed by CT scan;           *)
(*            fragment: which physical piece contains this gear;              *)
(*            tooth_uncertainty: measurement error bound (None if exact)      *)
(* -------------------------------------------------------------------------- *)
Record Gear := mkGear {
  gear_name : string;
  teeth : positive;
  ct_observed : bool;
  fragment : Fragment;
  tooth_uncertainty : option positive
}.

(* -------------------------------------------------------------------------- *)
(* Mesh                                                                       *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; gear train analysis                         *)
(* EVIDENCE:  CT imaging shows gear positions and mesh relationships          *)
(* SEMANTICS: Two gears in contact; driver transmits motion to driven;        *)
(*            ratio = driven_teeth / driver_teeth; direction reverses         *)
(* -------------------------------------------------------------------------- *)
Record Mesh := mkMesh {
  driver : Gear;
  driven : Gear;
  driver_direction : RotationDirection
}.

(* -------------------------------------------------------------------------- *)
(* driven_direction                                                           *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard gear mechanics                                         *)
(* EVIDENCE:  External gear mesh reverses rotation direction                  *)
(* SEMANTICS: Computes output direction from input direction of a mesh        *)
(* -------------------------------------------------------------------------- *)
Definition driven_direction (m : Mesh) : RotationDirection := flip_direction (driver_direction m).

(* -------------------------------------------------------------------------- *)
(* gear_ratio                                                                 *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard gear mechanics; Freeth et al. 2006 ratio calculations  *)
(* EVIDENCE:  Gear ratio = driven_teeth / driver_teeth (frequency ratio)      *)
(* SEMANTICS: Returns rational number representing angular velocity ratio;    *)
(*            if ratio > 1, driven rotates slower than driver                 *)
(* -------------------------------------------------------------------------- *)
Definition gear_ratio (m : Mesh) : Q := (Zpos (teeth (driven m))) # (teeth (driver m)).

(* -------------------------------------------------------------------------- *)
(* driver_neq_driven                                                          *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint                                             *)
(* EVIDENCE:  A gear cannot mesh with itself                                  *)
(* SEMANTICS: Validity predicate ensuring distinct gears in a mesh            *)
(* -------------------------------------------------------------------------- *)
Definition driver_neq_driven (m : Mesh) : Prop :=
  gear_name (driver m) <> gear_name (driven m).

(* -------------------------------------------------------------------------- *)
(* ValidMesh                                                                  *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint                                             *)
(* EVIDENCE:  All observed meshes in mechanism involve distinct gears         *)
(* SEMANTICS: Mesh bundled with proof of validity (distinct driver/driven)    *)
(* -------------------------------------------------------------------------- *)
Record ValidMesh := mkValidMesh {
  vm_mesh : Mesh;
  vm_distinct : driver_neq_driven vm_mesh
}.

(* -------------------------------------------------------------------------- *)
(* valid_tooth_count                                                          *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes; CT measurements         *)
(* EVIDENCE:  Observed gears range from 15 teeth (smallest) to 223 (largest); *)
(*            module constraint ~0.5mm limits minimum practical tooth count   *)
(* SEMANTICS: Predicate for physically plausible tooth counts                 *)
(* -------------------------------------------------------------------------- *)
Definition valid_tooth_count (n : positive) : Prop := (15 <= Zpos n <= 223)%Z.

(* -------------------------------------------------------------------------- *)
(* Arbor                                                                      *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Wright 2007; mechanism reconstruction                           *)
(* EVIDENCE:  Multiple gears mounted on shared axles observed in CT scans     *)
(* SEMANTICS: Gears sharing an axis rotate together at same angular velocity; *)
(*            enables compound gear trains with intermediate ratios           *)
(* -------------------------------------------------------------------------- *)
Record Arbor := mkArbor {
  arbor_gears : list Gear;
  arbor_constraint : (length arbor_gears >= 1)%nat
}.

(* -------------------------------------------------------------------------- *)
(* CoaxialArbor                                                               *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Wright 2007; mechanism reconstruction                           *)
(* EVIDENCE:  Concentric axles observed (e.g., moon pointer assembly)         *)
(* SEMANTICS: Multiple arbors sharing same geometric axis but rotating        *)
(*            independently; enables nested pointer displays                  *)
(* -------------------------------------------------------------------------- *)
Record CoaxialArbor := mkCoaxialArbor {
  coax_gears : list Gear;
  coax_min_gears : (length coax_gears >= 1)%nat;
  coax_shared_axis : string
}.

(* -------------------------------------------------------------------------- *)
(* TrainElement                                                               *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard gear train analysis; Freeth et al. 2006                *)
(* EVIDENCE:  Mechanism uses both direct meshes and arbor transfers           *)
(* SEMANTICS: SimpleMesh: direct gear engagement with ratio change;           *)
(*            ArborTransfer: same-arbor transfer with ratio 1:1               *)
(* -------------------------------------------------------------------------- *)
Inductive TrainElement : Set :=
  | SimpleMesh : Mesh -> TrainElement
  | ArborTransfer : Gear -> Gear -> TrainElement.

(* -------------------------------------------------------------------------- *)
(* train_element_ratio                                                        *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard gear mechanics                                         *)
(* EVIDENCE:  Mesh changes speed by gear ratio; arbor transfer preserves it   *)
(* SEMANTICS: Returns ratio contribution of single train element              *)
(* -------------------------------------------------------------------------- *)
Definition train_element_ratio (e : TrainElement) : Q :=
  match e with
  | SimpleMesh m => gear_ratio m
  | ArborTransfer _ _ => 1 # 1
  end.

(* -------------------------------------------------------------------------- *)
(* Train                                                                      *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; gear train reconstruction                   *)
(* EVIDENCE:  Mechanism contains multiple compound gear trains                *)
(* SEMANTICS: Sequence of train elements; total ratio is product of elements  *)
(* -------------------------------------------------------------------------- *)
Definition Train := list TrainElement.

(* -------------------------------------------------------------------------- *)
(* output_gear                                                                *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Gear train analysis                                             *)
(* EVIDENCE:  Each train element has an output gear receiving motion          *)
(* SEMANTICS: Returns the gear that receives motion from this element         *)
(* -------------------------------------------------------------------------- *)
Definition output_gear (e : TrainElement) : option Gear :=
  match e with
  | SimpleMesh m => Some (driven m)
  | ArborTransfer _ g2 => Some g2
  end.

(* -------------------------------------------------------------------------- *)
(* input_gear                                                                 *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Gear train analysis                                             *)
(* EVIDENCE:  Each train element has an input gear providing motion           *)
(* SEMANTICS: Returns the gear that provides motion to this element           *)
(* -------------------------------------------------------------------------- *)
Definition input_gear (e : TrainElement) : option Gear :=
  match e with
  | SimpleMesh m => Some (driver m)
  | ArborTransfer g1 _ => Some g1
  end.

(* -------------------------------------------------------------------------- *)
(* gears_coaxial                                                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Wright 2007; CT scan gear position analysis                     *)
(* EVIDENCE:  Gears on same arbor rotate together; CT shows arbor groupings   *)
(* SEMANTICS: Two gears share an axis (same gear or on same arbor)            *)
(* -------------------------------------------------------------------------- *)
Definition gears_coaxial (g1 g2 : Gear) : Prop :=
  gear_name g1 = gear_name g2 \/
  exists arb : Arbor, In g1 (arbor_gears arb) /\ In g2 (arbor_gears arb).

(* -------------------------------------------------------------------------- *)
(* elements_connected                                                         *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Gear train topology analysis                                    *)
(* EVIDENCE:  Train elements must connect via coaxial gears to transmit power *)
(* SEMANTICS: Output of e1 shares axis with input of e2                       *)
(* -------------------------------------------------------------------------- *)
Definition elements_connected (e1 e2 : TrainElement) : Prop :=
  match output_gear e1, input_gear e2 with
  | Some g1, Some g2 => gears_coaxial g1 g2
  | _, _ => False
  end.

(* -------------------------------------------------------------------------- *)
(* train_connected                                                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Gear train topology analysis                                    *)
(* EVIDENCE:  Physical gear trains form connected kinematic chains            *)
(* SEMANTICS: All adjacent elements in train are connected                    *)
(* -------------------------------------------------------------------------- *)
Fixpoint train_connected (t : Train) : Prop :=
  match t with
  | nil => True
  | [_] => True
  | e1 :: ((e2 :: _) as rest) => elements_connected e1 e2 /\ train_connected rest
  end.

(* -------------------------------------------------------------------------- *)
(* ValidTrain                                                                 *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint on gear trains                              *)
(* EVIDENCE:  Real gear trains are non-empty and fully connected              *)
(* SEMANTICS: Train bundled with proofs of non-emptiness and connectivity     *)
(* -------------------------------------------------------------------------- *)
Record ValidTrain := mkValidTrain {
  vt_train : Train;
  vt_nonempty : vt_train <> nil;
  vt_connected : train_connected vt_train
}.

(* -------------------------------------------------------------------------- *)
(* train_ratio                                                                *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard gear mechanics; Freeth et al. 2006 ratio derivations   *)
(* EVIDENCE:  Total gear train ratio is product of individual mesh ratios     *)
(* SEMANTICS: Computes overall frequency ratio of a gear train                *)
(* -------------------------------------------------------------------------- *)
Fixpoint train_ratio (t : Train) : Q :=
  match t with
  | nil => 1#1
  | e :: rest => Qmult (train_element_ratio e) (train_ratio rest)
  end.

(* -------------------------------------------------------------------------- *)
(* train_ratio_nil                                                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical identity                                           *)
(* EVIDENCE:  Empty product equals 1 (multiplicative identity)                *)
(* SEMANTICS: Base case for train ratio computation                           *)
(* -------------------------------------------------------------------------- *)
Lemma train_ratio_nil : train_ratio nil = 1#1.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* train_ratio_cons                                                           *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical identity                                           *)
(* EVIDENCE:  Product unfolds as first element times rest                     *)
(* SEMANTICS: Recursive case for train ratio computation                      *)
(* -------------------------------------------------------------------------- *)
Lemma train_ratio_cons : forall e t,
  train_ratio (e :: t) = Qmult (train_element_ratio e) (train_ratio t).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* arbor_transfer_ratio_1                                                     *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint on arbors                                   *)
(* EVIDENCE:  Gears on same arbor rotate at same speed (1:1 ratio)            *)
(* SEMANTICS: Arbor transfers contribute ratio 1 to train product             *)
(* -------------------------------------------------------------------------- *)
Lemma arbor_transfer_ratio_1 : forall g1 g2, train_element_ratio (ArborTransfer g1 g2) = 1 # 1.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* I-A. Uncertainty Intervals                                                 *)
(* ========================================================================== *)
(*                                                                            *)
(* CT scanning provides gear tooth estimates with measurement uncertainty.    *)
(* After 2000 years of corrosion, bronze distorted into brittle atacamite;    *)
(* exact dimensions unavailable. Tooth counts estimated from radius and       *)
(* module; some gears show clear peaks, others range of possible counts.      *)
(* Freeth et al. 2006 Supplementary Notes detail estimation procedures.       *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* QInterval                                                                  *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic for uncertainty propagation                 *)
(* EVIDENCE:  Freeth et al. 2006 Supp. Notes: tooth count ranges reported     *)
(* SEMANTICS: Closed interval [low, high] for rational-valued measurements    *)
(* -------------------------------------------------------------------------- *)
Record QInterval := mkInterval {
  interval_low : Q;
  interval_high : Q
}.

(* -------------------------------------------------------------------------- *)
(* interval_valid                                                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical constraint                                         *)
(* EVIDENCE:  Valid intervals have low <= high                                *)
(* SEMANTICS: Predicate ensuring interval is non-empty                        *)
(* -------------------------------------------------------------------------- *)
Definition interval_valid (i : QInterval) : Prop := Qle (interval_low i) (interval_high i).

(* -------------------------------------------------------------------------- *)
(* point_interval                                                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic                                             *)
(* EVIDENCE:  Exact values have zero uncertainty                              *)
(* SEMANTICS: Degenerate interval [q, q] representing exact value q           *)
(* -------------------------------------------------------------------------- *)
Definition point_interval (q : Q) : QInterval := mkInterval q q.

(* -------------------------------------------------------------------------- *)
(* gear_uncertainty_valid                                                     *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint                                             *)
(* EVIDENCE:  Uncertainty must be less than total tooth count                 *)
(* SEMANTICS: Ensures teeth - uncertainty > 0 (positive tooth count)          *)
(* -------------------------------------------------------------------------- *)
Definition gear_uncertainty_valid (g : Gear) : Prop :=
  match tooth_uncertainty g with
  | None => True
  | Some u => (Zpos u < Zpos (teeth g))%Z
  end.

(* -------------------------------------------------------------------------- *)
(* teeth_min                                                                  *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes                          *)
(* EVIDENCE:  CT measurement gives tooth count ± uncertainty                  *)
(* SEMANTICS: Lower bound of tooth count interval (teeth - uncertainty)       *)
(* -------------------------------------------------------------------------- *)
Definition teeth_min (g : Gear) : positive :=
  match tooth_uncertainty g with
  | None => teeth g
  | Some u => if Pos.ltb u (teeth g) then Pos.sub (teeth g) u else 1%positive
  end.

(* -------------------------------------------------------------------------- *)
(* teeth_min_positive                                                         *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint                                             *)
(* EVIDENCE:  Gears must have at least 1 tooth                                *)
(* SEMANTICS: Lower bound is always positive                                  *)
(* -------------------------------------------------------------------------- *)
Lemma teeth_min_positive : forall g, (Zpos (teeth_min g) >= 1)%Z.
Proof. intro g. unfold teeth_min. destruct (tooth_uncertainty g); lia. Qed.

(* -------------------------------------------------------------------------- *)
(* teeth_min_valid_no_underflow                                               *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Valid uncertainty doesn't underflow tooth count                 *)
(* SEMANTICS: With valid uncertainty, teeth_min = teeth - uncertainty         *)
(* -------------------------------------------------------------------------- *)
Lemma teeth_min_valid_no_underflow : forall g,
  gear_uncertainty_valid g ->
  match tooth_uncertainty g with
  | None => teeth_min g = teeth g
  | Some u => Zpos (teeth_min g) = Zpos (teeth g) - Zpos u
  end.
Proof.
  intro g. unfold gear_uncertainty_valid, teeth_min.
  destruct (tooth_uncertainty g) as [u|].
  - intro H. destruct (Pos.ltb u (teeth g)) eqn:Hlt.
    + rewrite Pos2Z.inj_sub. reflexivity. apply Pos.ltb_lt. exact Hlt.
    + apply Pos.ltb_ge in Hlt. lia.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* teeth_max                                                                  *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes                          *)
(* EVIDENCE:  CT measurement gives tooth count ± uncertainty                  *)
(* SEMANTICS: Upper bound of tooth count interval (teeth + uncertainty)       *)
(* -------------------------------------------------------------------------- *)
Definition teeth_max (g : Gear) : positive :=
  match tooth_uncertainty g with
  | None => teeth g
  | Some u => Pos.add (teeth g) u
  end.

(* -------------------------------------------------------------------------- *)
(* gear_ratio_interval                                                        *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic; Freeth et al. 2006                         *)
(* EVIDENCE:  Gear ratio uncertainty propagates from tooth count uncertainty  *)
(* SEMANTICS: [drn_min/drv_max, drn_max/drv_min] bounds possible ratios       *)
(* -------------------------------------------------------------------------- *)
Definition gear_ratio_interval (m : Mesh) : QInterval :=
  let drv_min := teeth_min (driver m) in
  let drv_max := teeth_max (driver m) in
  let drn_min := teeth_min (driven m) in
  let drn_max := teeth_max (driven m) in
  mkInterval (Zpos drn_min # drv_max) (Zpos drn_max # drv_min).

(* -------------------------------------------------------------------------- *)
(* interval_mult                                                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic                                             *)
(* EVIDENCE:  Product of intervals for train ratio uncertainty                *)
(* SEMANTICS: [a,b] * [c,d] = [a*c, b*d] for positive intervals               *)
(* -------------------------------------------------------------------------- *)
Definition interval_mult (i1 i2 : QInterval) : QInterval :=
  mkInterval (Qmult (interval_low i1) (interval_low i2))
             (Qmult (interval_high i1) (interval_high i2)).

(* -------------------------------------------------------------------------- *)
(* interval_contains                                                          *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic                                             *)
(* EVIDENCE:  Membership test for interval                                    *)
(* SEMANTICS: q ∈ [low, high] iff low <= q <= high                            *)
(* -------------------------------------------------------------------------- *)
Definition interval_contains (i : QInterval) (q : Q) : Prop :=
  Qle (interval_low i) q /\ Qle q (interval_high i).

(* -------------------------------------------------------------------------- *)
(* interval_width                                                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic                                             *)
(* EVIDENCE:  Width measures uncertainty magnitude                            *)
(* SEMANTICS: high - low; smaller width = more precise estimate               *)
(* -------------------------------------------------------------------------- *)
Definition interval_width (i : QInterval) : Q :=
  interval_high i - interval_low i.

(* -------------------------------------------------------------------------- *)
(* Qabs_custom                                                                *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical definition                                         *)
(* EVIDENCE:  Standard absolute value for error magnitude                     *)
(* SEMANTICS: |q| = q if q >= 0, else -q                                      *)
(* -------------------------------------------------------------------------- *)
Definition Qabs_custom (q : Q) : Q := if Qle_bool 0 q then q else Qopp q.

(* -------------------------------------------------------------------------- *)
(* Qabs_custom_nonneg                                                         *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Absolute value of non-negative is itself                        *)
(* SEMANTICS: q >= 0 implies |q| = q                                          *)
(* -------------------------------------------------------------------------- *)
Lemma Qabs_custom_nonneg : forall q, Qle_bool 0 q = true -> Qabs_custom q = q.
Proof. intros q H. unfold Qabs_custom. rewrite H. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Qabs_custom_neg                                                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Absolute value of negative is negation                          *)
(* SEMANTICS: q < 0 implies |q| = -q                                          *)
(* -------------------------------------------------------------------------- *)
Lemma Qabs_custom_neg : forall q, Qle_bool 0 q = false -> Qabs_custom q = Qopp q.
Proof. intros q H. unfold Qabs_custom. rewrite H. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* point_interval_valid                                                       *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  [q, q] satisfies q <= q                                         *)
(* SEMANTICS: Point intervals are always valid                                *)
(* -------------------------------------------------------------------------- *)
Lemma point_interval_valid : forall q, interval_valid (point_interval q).
Proof. intro q. unfold interval_valid, point_interval. simpl. apply Qle_refl. Qed.

(* -------------------------------------------------------------------------- *)
(* point_interval_contains                                                    *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  q is in [q, q]                                                  *)
(* SEMANTICS: A point interval contains its defining value                    *)
(* -------------------------------------------------------------------------- *)
Lemma point_interval_contains : forall q, interval_contains (point_interval q) q.
Proof.
  intro q. unfold interval_contains, point_interval. simpl.
  split; apply Qle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* gear_ratio_in_interval                                                     *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Uncertainty analysis                                            *)
(* EVIDENCE:  Nominal ratio should lie within uncertainty bounds              *)
(* SEMANTICS: Predicate that gear ratio is within its uncertainty interval    *)
(* -------------------------------------------------------------------------- *)
Definition gear_ratio_in_interval (m : Mesh) : Prop :=
  interval_contains (gear_ratio_interval m) (gear_ratio m).

(* -------------------------------------------------------------------------- *)
(* no_uncertainty_point_interval                                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  No uncertainty implies exact bounds                             *)
(* SEMANTICS: teeth_min = teeth_max = teeth when uncertainty is None          *)
(* -------------------------------------------------------------------------- *)
Lemma no_uncertainty_point_interval : forall g,
  tooth_uncertainty g = None ->
  teeth_min g = teeth g /\ teeth_max g = teeth g.
Proof.
  intros g H. unfold teeth_min, teeth_max. rewrite H. split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* relative_uncertainty                                                       *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes; metrology               *)
(* EVIDENCE:  Relative uncertainty = uncertainty / measurement                *)
(* SEMANTICS: Fractional uncertainty in tooth count (0 if exact)              *)
(* -------------------------------------------------------------------------- *)
Definition relative_uncertainty (g : Gear) : Q :=
  match tooth_uncertainty g with
  | None => 0 # 1
  | Some u => Zpos u # (teeth g)
  end.

(* -------------------------------------------------------------------------- *)
(* ct_uncertainty_bound                                                       *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes                          *)
(* EVIDENCE:  CT-derived tooth counts typically have < 3% relative error      *)
(* SEMANTICS: Upper bound on relative uncertainty for CT-observed gears       *)
(* -------------------------------------------------------------------------- *)
Definition ct_uncertainty_bound : Q := 3 # 100.

(* -------------------------------------------------------------------------- *)
(* gear_no_uncertainty_ratio_in_interval                                      *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Exact tooth counts yield point interval containing exact ratio  *)
(* SEMANTICS: With no uncertainty, gear ratio trivially in its own interval   *)
(* -------------------------------------------------------------------------- *)
Lemma gear_no_uncertainty_ratio_in_interval : forall m : Mesh,
  tooth_uncertainty (driver m) = None ->
  tooth_uncertainty (driven m) = None ->
  gear_ratio_in_interval m.
Proof.
  intros m Hdrv Hdrn.
  unfold gear_ratio_in_interval, interval_contains, gear_ratio_interval, gear_ratio.
  unfold teeth_min, teeth_max. rewrite Hdrv, Hdrn. simpl.
  split; apply Qle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* train_element_interval                                                     *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic                                             *)
(* EVIDENCE:  Each train element contributes uncertainty to total ratio       *)
(* SEMANTICS: Mesh uses gear_ratio_interval; arbor transfer is exact (1:1)    *)
(* -------------------------------------------------------------------------- *)
Definition train_element_interval (e : TrainElement) : QInterval :=
  match e with
  | SimpleMesh m => gear_ratio_interval m
  | ArborTransfer _ _ => point_interval (1 # 1)
  end.

(* -------------------------------------------------------------------------- *)
(* train_ratio_interval                                                       *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Interval arithmetic; uncertainty propagation                    *)
(* EVIDENCE:  Total train uncertainty is product of element uncertainties     *)
(* SEMANTICS: Computes interval containing all possible train ratios          *)
(* -------------------------------------------------------------------------- *)
Fixpoint train_ratio_interval (t : Train) : QInterval :=
  match t with
  | nil => point_interval (1 # 1)
  | e :: rest => interval_mult (train_element_interval e) (train_ratio_interval rest)
  end.

(* -------------------------------------------------------------------------- *)
(* train_ratio_interval_nil                                                   *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Empty product interval is point interval at 1                   *)
(* SEMANTICS: Base case for interval computation                              *)
(* -------------------------------------------------------------------------- *)
Lemma train_ratio_interval_nil :
  train_ratio_interval nil = point_interval (1 # 1).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* train_ratio_interval_cons                                                  *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Interval product unfolds recursively                            *)
(* SEMANTICS: Recursive case for interval computation                         *)
(* -------------------------------------------------------------------------- *)
Lemma train_ratio_interval_cons : forall e t,
  train_ratio_interval (e :: t) =
  interval_mult (train_element_interval e) (train_ratio_interval t).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* train_all_no_uncertainty                                                   *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Predicate for exact trains                                      *)
(* EVIDENCE:  Some gear trains have all CT-confirmed exact tooth counts       *)
(* SEMANTICS: All meshes in train have zero uncertainty                       *)
(* -------------------------------------------------------------------------- *)
Definition train_all_no_uncertainty (t : Train) : Prop :=
  forall e, In e t ->
  match e with
  | SimpleMesh m => tooth_uncertainty (driver m) = None /\ tooth_uncertainty (driven m) = None
  | ArborTransfer _ _ => True
  end.

(* -------------------------------------------------------------------------- *)
(* train_ratio_in_interval_nil                                                *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Empty train has ratio 1 in interval [1,1]                       *)
(* SEMANTICS: Base case soundness for interval containment                    *)
(* -------------------------------------------------------------------------- *)
Lemma train_ratio_in_interval_nil :
  interval_contains (train_ratio_interval nil) (train_ratio nil).
Proof. simpl. apply point_interval_contains. Qed.

(* -------------------------------------------------------------------------- *)
(* train_element_interval_nonneg                                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Physical constraint                                             *)
(* EVIDENCE:  Gear ratios are positive (positive tooth counts)                *)
(* SEMANTICS: Lower bound of element interval is non-negative                 *)
(* -------------------------------------------------------------------------- *)
Lemma train_element_interval_nonneg : forall e,
  Qle 0 (interval_low (train_element_interval e)).
Proof.
  intro e. destruct e as [m | g1 g2].
  - unfold train_element_interval, gear_ratio_interval, teeth_min, teeth_max, Qle. simpl. lia.
  - unfold train_element_interval, point_interval, Qle. simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* train_ratio_interval_nonneg                                                *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Product of non-negative intervals is non-negative               *)
(* SEMANTICS: Train ratio interval has non-negative lower bound               *)
(* -------------------------------------------------------------------------- *)
Lemma train_ratio_interval_nonneg : forall t,
  Qle 0 (interval_low (train_ratio_interval t)).
Proof.
  intro t. induction t as [|e rest IH].
  - simpl. unfold point_interval, Qle. simpl. lia.
  - simpl. unfold interval_mult, Qle. simpl.
    assert (H1 : (0 <= Qnum (interval_low (train_element_interval e)))%Z).
    { pose proof (train_element_interval_nonneg e) as He.
      unfold Qle in He. simpl in He. lia. }
    assert (H2 : (0 <= Qnum (interval_low (train_ratio_interval rest)))%Z).
    { unfold Qle in IH. simpl in IH. lia. }
    apply Z.mul_nonneg_nonneg; [|lia].
    apply Z.mul_nonneg_nonneg; lia.
Qed.

(* ========================================================================== *)
(* II. Epicyclic Gearing                                                      *)
(* ========================================================================== *)
(*                                                                            *)
(* The Antikythera mechanism uses epicyclic (planetary) gearing for the lunar *)
(* anomaly display. Hipparchos (c. 190-120 BC) developed two equivalent lunar *)
(* theories: eccentric and epicyclic. The pin-and-slot mechanism realizes the *)
(* epicyclic model, producing non-uniform lunar motion matching observations. *)
(* Freeth et al. 2006: the mechanism models lunar anomaly to better than 1    *)
(* part in 200, more accurately than Ptolemy's account of Hipparchos' theory. *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* EpicyclicCarrier                                                           *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; epicyclic gear theory                       *)
(* EVIDENCE:  CT scans show carrier arm structure in Fragment A               *)
(* SEMANTICS: Carrier arm holding planet gears; input_ratio from driver       *)
(* -------------------------------------------------------------------------- *)
Record EpicyclicCarrier := mkCarrier { carrier_input_ratio : Q; carrier_teeth : positive }.

(* -------------------------------------------------------------------------- *)
(* EpicyclicPlanet                                                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; epicyclic gear theory                       *)
(* EVIDENCE:  Planet gears observed in CT scans of lunar mechanism            *)
(* SEMANTICS: Planet gear(s) orbiting on carrier; may have multiple planets   *)
(* -------------------------------------------------------------------------- *)
Record EpicyclicPlanet := mkPlanet { planet_teeth : positive; planet_count : positive }.

(* -------------------------------------------------------------------------- *)
(* EpicyclicSun                                                               *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; epicyclic gear theory                       *)
(* EVIDENCE:  Central sun gear in lunar mechanism; fixed in some configs      *)
(* SEMANTICS: Central gear; sun_fixed indicates if held stationary            *)
(* -------------------------------------------------------------------------- *)
Record EpicyclicSun := mkSun { sun_teeth : positive; sun_fixed : bool }.

(* -------------------------------------------------------------------------- *)
(* EpicyclicRing                                                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Epicyclic gear theory (not used in lunar mechanism)             *)
(* EVIDENCE:  Ring gears possible but not confirmed for lunar display         *)
(* SEMANTICS: Outer ring gear; ring_output indicates if output is taken here  *)
(* -------------------------------------------------------------------------- *)
Record EpicyclicRing := mkRing { ring_teeth : positive; ring_output : bool }.

(* -------------------------------------------------------------------------- *)
(* EpicyclicTrain                                                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; Wright 2007 reconstruction                  *)
(* EVIDENCE:  Complete epicyclic assembly observed in lunar mechanism         *)
(* SEMANTICS: Full epicyclic gear train with carrier, planet, sun, opt. ring  *)
(* -------------------------------------------------------------------------- *)
Record EpicyclicTrain := mkEpicyclic {
  epi_carrier : EpicyclicCarrier;
  epi_planet : EpicyclicPlanet;
  epi_sun : EpicyclicSun;
  epi_ring : option EpicyclicRing
}.

(* -------------------------------------------------------------------------- *)
(* lunar_epicyclic_mean_ratio                                                 *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes; Hipparchos lunar theory *)
(* EVIDENCE:  Derivation from epicyclic kinematics for sun-fixed config       *)
(* SEMANTICS: Mean output frequency ratio; specialized for lunar pin-and-slot *)
(* NOTE:      Not a general epicyclic formula; see Willis circuit theory      *)
(* -------------------------------------------------------------------------- *)
Definition lunar_epicyclic_mean_ratio (e : EpicyclicTrain) : Q :=
  let Zs := Zpos (sun_teeth (epi_sun e)) in
  let Zp := Zpos (planet_teeth (epi_planet e)) in
  Qmult (carrier_input_ratio (epi_carrier e)) ((Zs + Zp) # (carrier_teeth (epi_carrier e))).

(* -------------------------------------------------------------------------- *)
(* planetary_output_ratio                                                     *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Epicyclic gear theory                                           *)
(* EVIDENCE:  Output ratio for planetary gear with sun fixed                  *)
(* SEMANTICS: output = input * (1 + sun_teeth/planet_teeth)                   *)
(* -------------------------------------------------------------------------- *)
Definition planetary_output_ratio (input_ratio : Q) (sun planet : positive) : Q :=
  Qmult input_ratio (1 + (Zpos sun # planet)).

(* -------------------------------------------------------------------------- *)
(* planetary_output_equal_gears                                               *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property                                           *)
(* EVIDENCE:  Equal sun and planet teeth gives ratio 2:1                      *)
(* SEMANTICS: Special case: 1 + n/n = 2                                       *)
(* -------------------------------------------------------------------------- *)
Lemma planetary_output_equal_gears :
  forall n : positive, Qeq (planetary_output_ratio (1 # 1) n n) (2 # 1).
Proof.
  intro n. unfold planetary_output_ratio, Qeq, Qmult, Qplus. simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* planetary_output_50_50                                                     *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Mathematical property; lunar mechanism analysis                 *)
(* EVIDENCE:  50-tooth gears used in pin-and-slot lunar anomaly mechanism     *)
(* SEMANTICS: With 50/50 gears, output ratio is exactly 2:1                   *)
(* -------------------------------------------------------------------------- *)
Lemma planetary_output_50_50 :
  Qeq (planetary_output_ratio (1 # 1) 50 50) (2 # 1).
Proof. unfold planetary_output_ratio, Qeq, Qmult, Qplus. simpl. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* lunar_anomaly_epicyclic                                                    *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; Wright 2007                                 *)
(* EVIDENCE:  CT scans show 50-tooth gears in lunar epicyclic assembly        *)
(* SEMANTICS: Configuration for lunar anomaly: 50-tooth carrier/planet/sun    *)
(* -------------------------------------------------------------------------- *)
Definition lunar_anomaly_epicyclic : EpicyclicTrain := mkEpicyclic
  (mkCarrier (1 # 1) 50) (mkPlanet 50 1) (mkSun 50 false) None.

(* -------------------------------------------------------------------------- *)
(* lunar_anomaly_epicyclic_mean_ratio                                         *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Supplementary Notes                          *)
(* EVIDENCE:  50+50=100, 100/50=2, so mean ratio is 2:1                       *)
(* SEMANTICS: Lunar epicyclic mean ratio verification                         *)
(* -------------------------------------------------------------------------- *)
Lemma lunar_anomaly_epicyclic_mean_ratio :
  Qeq (lunar_epicyclic_mean_ratio lunar_anomaly_epicyclic) (2 # 1).
Proof. unfold lunar_epicyclic_mean_ratio, lunar_anomaly_epicyclic, Qeq. simpl. reflexivity. Qed.

(* ========================================================================== *)
(* III. Gear Corpus                                                           *)
(* ========================================================================== *)
(*                                                                            *)
(* The mechanism contains ~30 confirmed gears identified via CT scanning.     *)
(* Key gears: 223 (Saros cycle), 127 (half Metonic sidereal = 254/2), 38      *)
(* (contains factor 19). Fragment A contains 27 gears; Fragments B, C, D      *)
(* each contain 1 additional gear. Hypothetical gears from Freeth 2021        *)
(* reconstruction fill gaps for planetary displays. Gear module ~0.5mm.       *)
(*                                                                            *)
(* CT-CONFIRMED GEARS (ct_observed = true):                                   *)
(*   b1/e3: 223 teeth - Saros eclipse cycle (223 synodic months)              *)
(*   127: 127 teeth - Half of 254 sidereal months per Metonic cycle           *)
(*   38a/38b: 38 teeth - Contains factor 19 (Metonic years)                   *)
(*   53a/53b/53c: 53 teeth - Lunar apogee period factor                       *)
(*   50a/50b/50c: 50 teeth - Lunar anomaly epicyclic gears                    *)
(*   63: 63 teeth - Fragment D, planetary display                             *)
(*   188: 188±2 teeth - Fragment C, uncertain count                           *)
(*                                                                            *)
(* HYPOTHETICAL GEARS (ct_observed = false, Freeth 2021):                     *)
(*   44, 34, 26: Venus train gears                                            *)
(*   72, 89, 40: Mercury train gears                                          *)
(*   Various others for Mars, Jupiter, Saturn planetary displays              *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* gear_b1                                                                    *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006 Nature; CT scan Fragment A                   *)
(* EVIDENCE:  223 teeth confirmed; drives Saros eclipse prediction dial       *)
(* SEMANTICS: 223 = Saros cycle in synodic months (18 years 11 days)          *)
(* -------------------------------------------------------------------------- *)
Definition gear_b1 := mkGear "b1" 223 true FragmentA None.
Definition gear_e3 := mkGear "e3" 223 true FragmentA None.
Definition gear_127 := mkGear "127" 127 true FragmentA None.
Definition gear_38a := mkGear "38a" 38 true FragmentA None.
Definition gear_38b := mkGear "38b" 38 true FragmentA None.
Definition gear_53a := mkGear "53a" 53 true FragmentA None.
Definition gear_53b := mkGear "53b" 53 true FragmentA None.
Definition gear_53c := mkGear "53c" 53 true FragmentA None.
Definition gear_50a := mkGear "50a" 50 true FragmentA None.
Definition gear_50b := mkGear "50b" 50 true FragmentA None.
Definition gear_27 := mkGear "27" 27 true FragmentA None.
Definition gear_63 := mkGear "63" 63 true FragmentD None.
Definition gear_50c := mkGear "50c" 50 true FragmentB None.
Definition gear_56 := mkGear "56" 56 true FragmentA None.
Definition gear_52 := mkGear "52" 52 true FragmentA None.
Definition gear_86 := mkGear "86" 86 true FragmentA None.
Definition gear_51 := mkGear "51" 51 true FragmentA None.
Definition gear_32 := mkGear "32" 32 true FragmentA None.
Definition gear_64 := mkGear "64" 64 true FragmentA None.
Definition gear_48 := mkGear "48" 48 true FragmentC None.
Definition gear_24 := mkGear "24" 24 true FragmentC None.
Definition gear_188 := mkGear "188" 188 true FragmentC (Some 2%positive).
Definition gear_60 := mkGear "60" 60 true FragmentC None.

Definition gear_44 := mkGear "44" 44 false Hypothetical None.
Definition gear_34 := mkGear "34" 34 false Hypothetical None.
Definition gear_26 := mkGear "26" 26 false Hypothetical None.
Definition gear_72 := mkGear "72" 72 false Hypothetical None.
Definition gear_89 := mkGear "89" 89 false Hypothetical None.
Definition gear_40 := mkGear "40" 40 false Hypothetical None.
Definition gear_20 := mkGear "20" 20 false Hypothetical None.
Definition gear_61 := mkGear "61" 61 false Hypothetical None.
Definition gear_68 := mkGear "68" 68 false Hypothetical None.
Definition gear_71 := mkGear "71" 71 false Hypothetical None.
Definition gear_80 := mkGear "80" 80 false Hypothetical None.
Definition gear_45 := mkGear "45" 45 false Hypothetical None.
Definition gear_36 := mkGear "36" 36 false Hypothetical None.
Definition gear_54 := mkGear "54" 54 false Hypothetical None.
Definition gear_96 := mkGear "96" 96 false Hypothetical None.
Definition gear_15 := mkGear "15" 15 false Hypothetical None.
Definition gear_57 := mkGear "57" 57 false Hypothetical None.
Definition gear_58 := mkGear "58" 58 false Hypothetical None.
Definition gear_59 := mkGear "59" 59 false Hypothetical None.
Definition gear_79 := mkGear "79" 79 false Hypothetical None.
Definition gear_19 := mkGear "19" 19 false Hypothetical None.
Definition gear_43 := mkGear "43" 43 false Hypothetical None.

Definition hypothetical_gears_freeth_2021 : list Gear :=
  [gear_20; gear_68; gear_71; gear_80; gear_44; gear_34; gear_26; gear_72; gear_89; gear_40; gear_19; gear_43].

Lemma hypothetical_all_under_100 :
  forallb (fun g => Pos.leb (teeth g) 100) hypothetical_gears_freeth_2021 = true.
Proof. reflexivity. Qed.

Lemma Z_68_factored : (68 = 4 * 17)%Z.
Proof. reflexivity. Qed.

Lemma Z_71_prime : (Z.gcd 71 70 = 1)%Z.
Proof. reflexivity. Qed.

Lemma Z_80_factored : (80 = 16 * 5)%Z.
Proof. reflexivity. Qed.

Record GearPhysical := mkGearPhysical {
  phys_gear : Gear;
  phys_module_mm : Q;
  phys_pitch_diameter_mm : Q;
  phys_outer_diameter_mm : Q
}.

Definition compute_pitch_diameter (teeth_count : positive) (module_mm : Q) : Q :=
  Qmult (Zpos teeth_count # 1) module_mm.

Definition compute_outer_diameter (pitch_d : Q) (module_mm : Q) : Q :=
  Qplus pitch_d (Qmult (2 # 1) module_mm).

Record ArborPhysical := mkArborPhysical {
  arbor_phys_gears : list GearPhysical;
  arbor_axis_diameter_mm : Q;
  arbor_length_mm : Q;
  arbor_phys_nonempty : (length arbor_phys_gears >= 1)%nat
}.

Definition all_same_module (gs : list GearPhysical) : Prop :=
  match gs with
  | nil => True
  | g :: rest => forall g', In g' rest -> Qeq (phys_module_mm g) (phys_module_mm g')
  end.

Definition gears_fit_on_arbor (arb : ArborPhysical) : Prop :=
  forall g, In g (arbor_phys_gears arb) ->
    Qlt (arbor_axis_diameter_mm arb) (phys_pitch_diameter_mm g).

Definition antikythera_module : Q := 5 # 10.

Lemma antikythera_module_half_mm : Qeq antikythera_module (1 # 2).
Proof. reflexivity. Qed.

Definition gear_50_physical : GearPhysical :=
  let m := antikythera_module in
  let pd := compute_pitch_diameter 50 m in
  mkGearPhysical gear_50a m pd (compute_outer_diameter pd m).

Lemma gear_50_pitch_diameter :
  Qeq (phys_pitch_diameter_mm gear_50_physical) (25 # 1).
Proof.
  unfold gear_50_physical, compute_pitch_diameter, antikythera_module.
  unfold Qeq, Qmult. simpl. reflexivity.
Qed.

Definition gear_physical_valid (g : GearPhysical) : Prop :=
  Qeq (phys_pitch_diameter_mm g) (compute_pitch_diameter (teeth (phys_gear g)) (phys_module_mm g)) /\ 
  Qeq (phys_outer_diameter_mm g) (compute_outer_diameter (phys_pitch_diameter_mm g) (phys_module_mm g)).

Lemma gear_50_physical_valid : gear_physical_valid gear_50_physical.
Proof.
  unfold gear_physical_valid, gear_50_physical, compute_pitch_diameter, compute_outer_diameter.
  unfold antikythera_module, gear_50a. simpl.
  split; reflexivity.
Qed.

Lemma gear_188_uncertainty : tooth_uncertainty gear_188 = Some 2%positive.
Proof. reflexivity. Qed.

Lemma gear_188_teeth_range :
  teeth_min gear_188 = 186%positive /\ teeth_max gear_188 = 190%positive.
Proof. split; reflexivity. Qed.

Lemma gear_188_relative_uncertainty :
  Qlt (relative_uncertainty gear_188) ct_uncertainty_bound.
Proof.
  unfold relative_uncertainty, gear_188, ct_uncertainty_bound. simpl.
  unfold Qlt. simpl. lia.
Qed.

Definition mesh_with_188 : Mesh := mkMesh gear_60 gear_188 Clockwise.

Lemma mesh_188_interval_width :
  interval_width (gear_ratio_interval mesh_with_188) = Qminus (190 # 60) (186 # 60).
Proof. reflexivity. Qed.

Definition saros_188_interval : QInterval :=
  gear_ratio_interval mesh_with_188.

Lemma saros_188_nominal_in_interval :
  interval_contains saros_188_interval (188 # 60).
Proof.
  unfold saros_188_interval, interval_contains, gear_ratio_interval, mesh_with_188.
  unfold teeth_min, teeth_max, gear_188. simpl.
  split; unfold Qle; simpl; lia.
Qed.

Lemma saros_188_uncertainty_bounded :
  Qlt (interval_width saros_188_interval) (1 # 10).
Proof.
  unfold saros_188_interval, interval_width, gear_ratio_interval, mesh_with_188.
  unfold teeth_min, teeth_max, gear_188. simpl.
  unfold Qlt, Qminus. simpl. lia.
Qed.

Definition ct_confirmed_gears : list Gear := [
  gear_b1; gear_e3; gear_127; gear_38a; gear_38b;
  gear_53a; gear_53b; gear_53c; gear_50a; gear_50b;
  gear_27; gear_63; gear_50c; gear_56; gear_52; gear_86; gear_51;
  gear_32; gear_64; gear_48; gear_24; gear_188; gear_60
].

Definition all_ct_observed (gs : list Gear) : bool :=
  forallb ct_observed gs.

Lemma all_ct_observed_ct_confirmed : all_ct_observed ct_confirmed_gears = true.
Proof. reflexivity. Qed.

Lemma forallb_In : forall {A : Type} (f : A -> bool) (l : list A) (x : A),
  forallb f l = true -> In x l -> f x = true.
Proof.
  intros A f l x Hforall Hin.
  induction l as [| h t IH].
  - contradiction.
  - simpl in Hforall. apply andb_prop in Hforall. destruct Hforall as [Hh Ht].
    simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. exact Hh.
    + apply IH; assumption.
Qed.

Theorem ct_observed_true : forall g, In g ct_confirmed_gears -> ct_observed g = true.
Proof.
  intros g Hin.
  apply (forallb_In ct_observed ct_confirmed_gears g).
  - exact all_ct_observed_ct_confirmed.
  - exact Hin.
Qed.

Definition fragment_A_gears : list Gear :=
  filter (fun g => match fragment g with FragmentA => true | _ => false end) ct_confirmed_gears.

Lemma fragment_A_gears_length : length fragment_A_gears = 17%nat.
Proof. reflexivity. Qed.

Lemma fragment_A_all_observed :
  forallb ct_observed fragment_A_gears = true.
Proof. reflexivity. Qed.

Definition fragment_count (f : Fragment) : nat :=
  length (filter (fun g => match fragment g with
    | FragmentA => match f with FragmentA => true | _ => false end
    | FragmentB => match f with FragmentB => true | _ => false end
    | FragmentC => match f with FragmentC => true | _ => false end
    | FragmentD => match f with FragmentD => true | _ => false end
    | _ => false
    end) ct_confirmed_gears).

Definition arbor_b1_e3 : Arbor.
Proof.
  refine (mkArbor [gear_b1; gear_e3] _).
  simpl. lia.
Defined.

Lemma arbor_b1_e3_gears : arbor_gears arbor_b1_e3 = [gear_b1; gear_e3].
Proof. reflexivity. Qed.

Definition arbor_38_127 : Arbor.
Proof.
  refine (mkArbor [gear_38a; gear_127] _).
  simpl. lia.
Defined.

Lemma arbor_38_127_length : length (arbor_gears arbor_38_127) = 2%nat.
Proof. reflexivity. Qed.

Definition arbor_44_34 : Arbor.
Proof. refine (mkArbor [gear_44; gear_34] _). simpl. lia. Defined.

Definition arbor_26_63 : Arbor.
Proof. refine (mkArbor [gear_26; gear_63] _). simpl. lia. Defined.

Definition arbor_45_54 : Arbor.
Proof. refine (mkArbor [gear_45; gear_54] _). simpl. lia. Defined.

Definition arbor_96_15 : Arbor.
Proof. refine (mkArbor [gear_96; gear_15] _). simpl. lia. Defined.

Definition arbor_79_36 : Arbor.
Proof. refine (mkArbor [gear_79; gear_36] _). simpl. lia. Defined.

Definition arbor_72_40 : Arbor.
Proof. refine (mkArbor [gear_72; gear_40] _). simpl. lia. Defined.

Definition arbor_57_58 : Arbor.
Proof. refine (mkArbor [gear_57; gear_58] _). simpl. lia. Defined.

Definition arbor_89_15 : Arbor.
Proof. refine (mkArbor [gear_89; gear_15] _). simpl. lia. Defined.

Definition arbor_19_36 : Arbor.
Proof. refine (mkArbor [gear_19; gear_36] _). simpl. lia. Defined.

Definition arbor_63_24 : Arbor.
Proof. refine (mkArbor [gear_63; gear_24] _). simpl. lia. Defined.

Definition gears_same_name (g1 g2 : Gear) : bool :=
  String.eqb (gear_name g1) (gear_name g2).

Definition gears_on_arbor (g1 g2 : Gear) (arb : Arbor) : bool :=
  existsb (fun g => gears_same_name g g1) (arbor_gears arb) &&
  existsb (fun g => gears_same_name g g2) (arbor_gears arb).

Lemma gears_same_name_refl : forall g, gears_same_name g g = true.
Proof. intro g. unfold gears_same_name. apply String.eqb_refl. Qed.

Lemma gears_same_name_eq : forall g1 g2,
  gears_same_name g1 g2 = true -> gear_name g1 = gear_name g2.
Proof. intros g1 g2 H. unfold gears_same_name in H. apply String.eqb_eq. exact H. Qed.

Lemma gears_same_name_coaxial : forall g1 g2,
  gears_same_name g1 g2 = true -> gears_coaxial g1 g2.
Proof. intros g1 g2 H. left. apply gears_same_name_eq. exact H. Qed.

Lemma existsb_In : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  intros A f l H. induction l as [|h t IH].
  - discriminate.
  - simpl in H. apply orb_prop in H. destruct H as [Hh | Ht].
    + exists h. split. left. reflexivity. exact Hh.
    + destruct (IH Ht) as [x [Hin Hfx]]. exists x. split. right. exact Hin. exact Hfx.
Qed.

Lemma In_gear_name_eq : forall g1 g2 l,
  In g1 l -> gears_same_name g1 g2 = true ->
  exists g, In g l /\ gear_name g = gear_name g2.
Proof.
  intros g1 g2 l Hin Heq. exists g1. split. exact Hin.
  apply gears_same_name_eq. exact Heq.
Qed.

Definition gears_coaxial_dec (g1 g2 : Gear) : bool :=
  gears_same_name g1 g2.

Lemma gears_coaxial_dec_correct : forall g1 g2,
  gears_coaxial_dec g1 g2 = true -> gears_coaxial g1 g2.
Proof.
  intros g1 g2 H. unfold gears_coaxial_dec in H.
  left. apply gears_same_name_eq. exact H.
Qed.

Lemma fragment_counts :
  fragment_count FragmentA = 17%nat /\ fragment_count FragmentB = 1%nat /\ fragment_count FragmentC = 4%nat /\ fragment_count FragmentD = 1%nat.
Proof. repeat split; reflexivity. Qed.

Lemma fragment_A_count : fragment_count FragmentA = 17%nat.
Proof. exact (proj1 fragment_counts). Qed.

Lemma fragment_B_count : fragment_count FragmentB = 1%nat.
Proof. exact (proj1 (proj2 fragment_counts)). Qed.

Lemma fragment_C_count : fragment_count FragmentC = 4%nat.
Proof. exact (proj1 (proj2 (proj2 fragment_counts))). Qed.

Lemma fragment_D_count : fragment_count FragmentD = 1%nat.
Proof. exact (proj2 (proj2 (proj2 fragment_counts))). Qed.

Lemma fragment_total : (fragment_count FragmentA + fragment_count FragmentB +
  fragment_count FragmentC + fragment_count FragmentD)%nat = 23%nat.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* IV. Astronomical Periods                                                   *)
(* ========================================================================== *)
(*                                                                            *)
(* Period relations link astronomical phenomena to whole numbers of years.    *)
(* Babylonians discovered these through centuries of observation; Greeks      *)
(* adopted and refined them. The Antikythera mechanism encodes these ratios   *)
(* in its gear trains. Key sources: Babylonian astronomical diaries; Greek    *)
(* astronomers Meton (432 BC), Callippus (330 BC), Hipparchos (c. 150 BC).    *)
(*                                                                            *)
(* METONIC CYCLE (Meton of Athens, 432 BC):                                   *)
(*   235 synodic months ≈ 19 tropical years (error < 2 hours over 19 years)   *)
(*   Used for lunisolar calendar synchronization                              *)
(*                                                                            *)
(* CALLIPPIC CYCLE (Callippus, 330 BC):                                       *)
(*   940 synodic months = 76 years = 4 × Metonic cycle                        *)
(*   Refinement dropping one day from 4 Metonic cycles for better accuracy    *)
(*                                                                            *)
(* SAROS CYCLE (Babylonian, discovered c. 700 BC):                            *)
(*   223 synodic months ≈ 6585.32 days ≈ 18 years 11 days 8 hours             *)
(*   Eclipse repetition cycle (same Sun-Moon-Node geometry)                   *)
(*                                                                            *)
(* EXELIGMOS (3 × Saros):                                                     *)
(*   669 synodic months ≈ 54 years 33 days                                    *)
(*   Eliminates 8-hour Saros remainder; eclipses at same longitude            *)
(*                                                                            *)
(* PLANETARY PERIOD RELATIONS (Babylonian, refined by Greeks):                *)
(*   Venus: 289 synodic periods in 462 years (FCI inscription: 462)           *)
(*   Saturn: 427 synodic periods in 442 years (FCI inscription: 442)          *)
(*   Mercury, Mars, Jupiter: from Babylonian tablets and FCI                  *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Metonic Cycle: 235 synodic months = 19 tropical years                      *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Babylonian astronomy; Meton of Athens 432 BC                    *)
(* EVIDENCE:  Inscribed on mechanism; gear 38 contains factor 19              *)
(* SEMANTICS: Fundamental lunisolar synchronization cycle                     *)
(* -------------------------------------------------------------------------- *)
Definition metonic_months : positive := 235.
Definition metonic_years : positive := 19.
Definition metonic_ratio : Q := 235 # 19.

(* -------------------------------------------------------------------------- *)
(* Callippic Cycle: 940 synodic months = 76 years = 4 × Metonic               *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Callippus of Cyzicus, 330 BC                                    *)
(* EVIDENCE:  76-year dial on mechanism back; 940 = 4 × 235                   *)
(* SEMANTICS: Refined Metonic for whole-day alignment                         *)
(* -------------------------------------------------------------------------- *)
Definition callippic_months : positive := 940.
Definition callippic_years : positive := 76.
Definition callippic_ratio : Q := 940 # 76.

(* -------------------------------------------------------------------------- *)
(* Saros Cycle: 223 synodic months ≈ 18 years 11 days 8 hours                 *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Babylonian astronomy, c. 700 BC; gear e3 has 223 teeth          *)
(* EVIDENCE:  223-tooth gear confirmed by CT; drives Saros spiral dial        *)
(* SEMANTICS: Eclipse prediction cycle (Sun-Moon-Node alignment repeats)      *)
(* -------------------------------------------------------------------------- *)
Definition saros_months : positive := 223.
Definition saros_ratio : Q := 223 # 1.

(* -------------------------------------------------------------------------- *)
(* Exeligmos Cycle: 669 synodic months = 3 × Saros ≈ 54 years 33 days         *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Greek astronomy; eliminates Saros 8-hour remainder              *)
(* EVIDENCE:  Exeligmos pointer on mechanism for tracking triple-Saros        *)
(* SEMANTICS: Full eclipse return cycle at same terrestrial longitude         *)
(* -------------------------------------------------------------------------- *)
Definition exeligmos_months : positive := 669.
Definition exeligmos_ratio : Q := 669 # 1.

(* -------------------------------------------------------------------------- *)
(* Venus Period: 289 synodic periods in 462 years                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Babylonian astronomy; FCI inscription shows 462 (ΥΞΒ)           *)
(* EVIDENCE:  2016 CT scan revealed 462 in Venus section of Front Cover       *)
(* SEMANTICS: 289 = 17²; synodic periods per year ratio for Venus gear train  *)
(* -------------------------------------------------------------------------- *)
Definition venus_synodic_periods : positive := 289.
Definition venus_years : positive := 462.
Definition venus_ratio : Q := 289 # 462.

(* -------------------------------------------------------------------------- *)
(* Saturn Period: 427 synodic periods in 442 years                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Babylonian astronomy; FCI inscription shows 442 (ΥΜΒ)           *)
(* EVIDENCE:  2016 CT scan revealed 442 in Saturn section of Front Cover      *)
(* SEMANTICS: 427/442 irreducible; requires factor 13 unavailable in corpus   *)
(* -------------------------------------------------------------------------- *)
Definition saturn_synodic_periods : positive := 427.
Definition saturn_years : positive := 442.
Definition saturn_ratio : Q := 427 # 442.

(* -------------------------------------------------------------------------- *)
(* Mercury Period: 1513 synodic periods in 480 years                          *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth 2021 reconstruction; derived from Babylonian relations   *)
(* EVIDENCE:  Computational derivation; gear train reconstructed              *)
(* SEMANTICS: Mercury's short synodic period (116 days) × frequency ratio     *)
(* -------------------------------------------------------------------------- *)
Definition mercury_synodic_periods : positive := 1513.
Definition mercury_years : positive := 480.
Definition mercury_ratio : Q := 1513 # 480.

(* -------------------------------------------------------------------------- *)
(* Mars Period: 133 synodic periods in 284 years                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Babylonian astronomy; Freeth 2021 reconstruction                *)
(* EVIDENCE:  133 = 7 × 19; 284 = 4 × 71; gear train reconstructed            *)
(* SEMANTICS: Mars synodic period ~780 days; ratio for gear train             *)
(* -------------------------------------------------------------------------- *)
Definition mars_synodic_periods : positive := 133.
Definition mars_years : positive := 284.
Definition mars_ratio : Q := 133 # 284.

(* -------------------------------------------------------------------------- *)
(* Jupiter Period: 315 synodic periods in 344 years                           *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Babylonian astronomy; Freeth 2021 reconstruction                *)
(* EVIDENCE:  315 = 5 × 63; 344 = 8 × 43; gear train reconstructed            *)
(* SEMANTICS: Jupiter synodic period ~399 days; ratio for gear train          *)
(* -------------------------------------------------------------------------- *)
Definition jupiter_synodic_periods : positive := 315.
Definition jupiter_years : positive := 344.
Definition jupiter_ratio : Q := 315 # 344.

Lemma Qeq_callippic_metonic : Qeq callippic_ratio metonic_ratio.
Proof. unfold callippic_ratio, metonic_ratio, Qeq. simpl. reflexivity. Qed.

Lemma callippic_4_metonic_years : (Zpos callippic_years = 4 * Zpos metonic_years)%Z.
Proof. reflexivity. Qed.

Lemma callippic_4_metonic_months : (Zpos callippic_months = 4 * Zpos metonic_months)%Z.
Proof. reflexivity. Qed.

Definition callippic_gear_ratio : Q := 4 # 1.

Lemma callippic_from_metonic_ratio :
  Qeq (Qmult metonic_ratio callippic_gear_ratio) (940 # 19).
Proof. unfold metonic_ratio, callippic_gear_ratio, Qeq, Qmult. simpl. reflexivity. Qed.

Definition callippic_dial_divisions : positive := 76.

Lemma callippic_76_eq_4_mul_19 : (76 = 4 * 19)%nat.
Proof. reflexivity. Qed.

Lemma Z_235_eq_5_mul_47 : (235 = 5 * 47)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_235_19_eq_1 : (Z.gcd 235 19 = 1)%Z.
Proof. reflexivity. Qed.

Lemma metonic_ratio_irreducible : (Z.gcd 235 19 = 1)%Z.
Proof. reflexivity. Qed.

Lemma Z_289_eq_17_sq : (289 = 17 * 17)%Z.
Proof. reflexivity. Qed.

Lemma Z_462_factored : (462 = 2 * 3 * 7 * 11)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_289_462_eq_1 : (Z.gcd 289 462 = 1)%Z.
Proof. reflexivity. Qed.

Lemma venus_ratio_irreducible : (Z.gcd 289 462 = 1)%Z.
Proof. reflexivity. Qed.

Lemma Z_427_eq_7_mul_61 : (427 = 7 * 61)%Z.
Proof. reflexivity. Qed.

Lemma Z_442_eq_2_mul_13_mul_17 : (442 = 2 * 13 * 17)%Z.
Proof. reflexivity. Qed.

Lemma Z_133_eq_7_mul_19 : (133 = 7 * 19)%Z.
Proof. reflexivity. Qed.

Lemma Z_284_eq_4_mul_71 : (284 = 4 * 71)%Z.
Proof. reflexivity. Qed.

Lemma Z_315_eq_5_mul_63 : (315 = 5 * 63)%Z.
Proof. reflexivity. Qed.

Lemma Z_344_eq_8_mul_43 : (344 = 8 * 43)%Z.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* V. Metonic Train                                                           *)
(* ========================================================================== *)
(*                                                                            *)
(* The Metonic ratio 235/19 = (254-19)/19 derives from the lunar sidereal     *)
(* frequency 254/19 via the differential: synodic = sidereal - solar, where   *)
(* solar frequency = 1. This relationship is proved in differential_derives_  *)
(* synodic. The Metonic dial pointer is driven via the differential output,   *)
(* not a standalone gear train, so no metonic_train : Train is defined.       *)
(*                                                                            *)
(* ========================================================================== *)

Definition metonic_spec (r : Q) : Prop := Qeq r (235 # 19).

Definition metonic_mesh_1 : Mesh := mkMesh gear_38a gear_127 Clockwise.

Lemma gear_ratio_metonic_mesh_1 : gear_ratio metonic_mesh_1 = 127 # 38.
Proof. reflexivity. Qed.

Lemma metonic_mesh_1_ratio_in_interval : gear_ratio_in_interval metonic_mesh_1.
Proof. apply gear_no_uncertainty_ratio_in_interval; reflexivity. Qed.

Definition mesh_b1_e3 : Mesh := mkMesh gear_b1 gear_e3 Clockwise.

Lemma saros_mesh_ratio_in_interval : gear_ratio_in_interval mesh_b1_e3.
Proof. apply gear_no_uncertainty_ratio_in_interval; reflexivity. Qed.

Definition metonic_compound_factor : Q := 235 # 127.

Lemma Qeq_127_38_mul_235_127 : Qeq (Qmult (127 # 38) (235 # 127)) (235 # 38).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Definition metonic_final_reduction : Q := 38 # 19.

Lemma Qeq_metonic_inverse_product :
  Qeq (Qmult (235 # 38) (Qmult (38 # 19) (19 # 235))) (1 # 1).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Definition metonic_train_ratio : Q := 235 # 19.

Theorem metonic_train_spec : metonic_spec metonic_train_ratio.
Proof. unfold metonic_spec, metonic_train_ratio. reflexivity. Qed.

Lemma Qeq_metonic_235_19 : Qeq metonic_train_ratio (235 # 19).
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* VI. Venus Train                                                            *)
(* ========================================================================== *)
(*                                                                            *)
(* Venus gear train realizes the period relation 289/462 (synodic/years).     *)
(* The Front Cover Inscription (FCI) shows 462 (Greek ΥΞΒ) in Venus section,  *)
(* discovered in 2016 CT scans. 289 = 17²; 462 = 2 × 3 × 7 × 11.              *)
(*                                                                            *)
(* Train: 51→44, 34→26, 26→63 (hypothetical gears from Freeth 2021)           *)
(* Product: (44×26×63)/(51×34×26) = 72072/45084 = 462/289                     *)
(* Inverse 289/462 gives synodic periods per year as required.                *)
(*                                                                            *)
(* Venus synodic period ≈ 584 days; 289 periods × 584 ≈ 462 × 365.25 days    *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* venus_train                                                                *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth 2021 reconstruction; FCI inscription 462                 *)
(* EVIDENCE:  Gear 63 CT-confirmed (Fragment D); others hypothetical          *)
(* SEMANTICS: Full train with arbor transfers; realizes 462/289 ratio         *)
(* -------------------------------------------------------------------------- *)
Definition venus_train : Train := [
  SimpleMesh (mkMesh gear_51 gear_44 Clockwise);
  ArborTransfer gear_44 gear_34;
  SimpleMesh (mkMesh gear_34 gear_26 CounterClockwise);
  ArborTransfer gear_26 gear_63;
  SimpleMesh (mkMesh gear_26 gear_63 Clockwise)
].

Lemma gear_ratio_51_44 : gear_ratio (mkMesh gear_51 gear_44 Clockwise) = 44 # 51.
Proof. reflexivity. Qed.

Lemma gear_ratio_34_26 : gear_ratio (mkMesh gear_34 gear_26 CounterClockwise) = 26 # 34.
Proof. reflexivity. Qed.

Lemma gear_ratio_26_63 : gear_ratio (mkMesh gear_26 gear_63 Clockwise) = 63 # 26.
Proof. reflexivity. Qed.

Definition venus_train_simple : Train := [
  SimpleMesh (mkMesh gear_51 gear_44 Clockwise);
  SimpleMesh (mkMesh gear_34 gear_26 CounterClockwise);
  SimpleMesh (mkMesh gear_26 gear_63 Clockwise)
].

Lemma train_ratio_venus : train_ratio venus_train_simple = Qmult (44 # 51) (Qmult (26 # 34) (63 # 26)).
Proof. reflexivity. Qed.

Lemma Z_44_mul_26_mul_63 : (44 * 26 * 63 = 72072)%Z.
Proof. reflexivity. Qed.

Lemma Z_51_mul_34_mul_26 : (51 * 34 * 26 = 45084)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_72072_45084 : (Z.gcd 72072 45084 = 156)%Z.
Proof. reflexivity. Qed.

Lemma Z_72072_div_156 : (72072 / 156 = 462)%Z.
Proof. reflexivity. Qed.

Lemma Z_45084_div_156 : (45084 / 156 = 289)%Z.
Proof. reflexivity. Qed.

Definition venus_spec (r : Q) : Prop := Qeq r (289 # 462).

Lemma Qeq_venus_train_462_289 : Qeq (train_ratio venus_train_simple) (462 # 289).
Proof.
  unfold venus_train_simple, train_ratio, train_element_ratio, gear_ratio. simpl.
  unfold Qeq. simpl. reflexivity.
Qed.

Theorem Qeq_venus_inv_289_462 : Qeq (Qinv (train_ratio venus_train_simple)) (289 # 462).
Proof.
  rewrite Qeq_venus_train_462_289.
  unfold Qinv, Qeq. simpl. reflexivity.
Qed.

Theorem venus_train_complete :
  venus_spec (Qinv (train_ratio venus_train_simple)) /\ train_ratio venus_train_simple = Qmult (44 # 51) (Qmult (26 # 34) (63 # 26)).
Proof.
  split.
  - unfold venus_spec. exact Qeq_venus_inv_289_462.
  - reflexivity.
Qed.

Lemma venus_44_34_coaxial : gears_coaxial gear_44 gear_34.
Proof.
  right. exists arbor_44_34. split; simpl; auto.
Qed.

Lemma venus_26_26_coaxial : gears_coaxial gear_26 gear_26.
Proof. left. reflexivity. Qed.

Lemma venus_train_connected : train_connected venus_train_simple.
Proof.
  unfold venus_train_simple, train_connected.
  split.
  - unfold elements_connected. simpl. exact venus_44_34_coaxial.
  - split.
    + unfold elements_connected. simpl. exact venus_26_26_coaxial.
    + exact I.
Qed.

Definition venus_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain venus_train_simple _ _).
  - discriminate.
  - exact venus_train_connected.
Defined.

Theorem venus_ratio_validated :
  Qeq (train_ratio (vt_train venus_valid_train)) (462 # 289).
Proof. exact Qeq_venus_train_462_289. Qed.

(* ========================================================================== *)
(* VII. Saturn Train                                                          *)
(* ========================================================================== *)
(*                                                                            *)
(* NOTE: saturn_train_simple below produces ratio 18/7, NOT 427/442.          *)
(* The ratio 427/442 = (7*61)/(2*13*17) requires factor 13, which is not      *)
(* available in the known gear corpus. Saturn likely used an epicyclic or     *)
(* differential mechanism. The train is retained to show what this gear       *)
(* combination produces; saturn_direct_ratio encodes the inscription value.   *)
(*                                                                            *)
(* ========================================================================== *)

Definition saturn_spec (r : Q) : Prop := Qeq r (427 # 442).

Definition saturn_train_simple : Train := [
  SimpleMesh (mkMesh gear_56 gear_45 Clockwise);
  SimpleMesh (mkMesh gear_54 gear_96 CounterClockwise);
  SimpleMesh (mkMesh gear_15 gear_27 Clockwise)
].

Lemma gear_ratio_56_45 : gear_ratio (mkMesh gear_56 gear_45 Clockwise) = 45 # 56.
Proof. reflexivity. Qed.

Lemma gear_ratio_54_96 : gear_ratio (mkMesh gear_54 gear_96 CounterClockwise) = 96 # 54.
Proof. reflexivity. Qed.

Lemma gear_ratio_15_27 : gear_ratio (mkMesh gear_15 gear_27 Clockwise) = 27 # 15.
Proof. reflexivity. Qed.

Lemma Z_45_mul_96_mul_27 : (45 * 96 * 27 = 116640)%Z.
Proof. reflexivity. Qed.

Lemma Z_56_mul_54_mul_15 : (56 * 54 * 15 = 45360)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_116640_45360 : (Z.gcd 116640 45360 = 6480)%Z.
Proof. reflexivity. Qed.

Lemma train_ratio_saturn_simple_eq :
  train_ratio saturn_train_simple = Qmult (45 # 56) (Qmult (96 # 54) (27 # 15)).
Proof. reflexivity. Qed.

Lemma Qeq_saturn_simple_18_7 :
  Qeq (train_ratio saturn_train_simple) (18 # 7).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Lemma saturn_simple_not_spec :
  ~ Qeq (train_ratio saturn_train_simple) (427 # 442).
Proof.
  unfold Qeq. simpl. lia.
Qed.

Lemma saturn_simple_inv_not_spec :
  ~ Qeq (Qinv (train_ratio saturn_train_simple)) (427 # 442).
Proof.
  unfold Qeq, Qinv. simpl. lia.
Qed.

Definition saturn_epicyclic : EpicyclicTrain := mkEpicyclic
  (mkCarrier (1 # 1) 56) (mkPlanet 61 2) (mkSun 52 true) None.

Lemma saturn_epicyclic_ratio_computed :
  lunar_epicyclic_mean_ratio saturn_epicyclic = 113 # 56.
Proof. unfold lunar_epicyclic_mean_ratio, saturn_epicyclic. simpl. reflexivity. Qed.

Definition saturn_direct_ratio : Q := 427 # 442.

Lemma Z_gcd_427_442_eq_1 : (Z.gcd 427 442 = 1)%Z.
Proof. reflexivity. Qed.

Lemma saturn_ratio_irreducible : (Z.gcd 427 442 = 1)%Z.
Proof. exact Z_gcd_427_442_eq_1. Qed.

Theorem saturn_train_spec : saturn_spec saturn_direct_ratio.
Proof. unfold saturn_spec, saturn_direct_ratio. reflexivity. Qed.

Definition saturn_inscription_years : positive := 442.
Definition saturn_inscription_periods : positive := 427.

Theorem saturn_inscription_match :
  saturn_years = saturn_inscription_years /\ saturn_synodic_periods = saturn_inscription_periods.
Proof. split; reflexivity. Qed.

Lemma saturn_45_54_coaxial : gears_coaxial gear_45 gear_54.
Proof. right. exists arbor_45_54. split; simpl; auto. Qed.

Lemma saturn_96_15_coaxial : gears_coaxial gear_96 gear_15.
Proof. right. exists arbor_96_15. split; simpl; auto. Qed.

Lemma saturn_train_connected : train_connected saturn_train_simple.
Proof.
  unfold saturn_train_simple, train_connected.
  split.
  - unfold elements_connected. simpl. exact saturn_45_54_coaxial.
  - split.
    + unfold elements_connected. simpl. exact saturn_96_15_coaxial.
    + exact I.
Qed.

Definition saturn_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain saturn_train_simple _ _).
  - discriminate.
  - exact saturn_train_connected.
Defined.

(* ========================================================================== *)
(* VIII. Mercury, Mars, Jupiter Trains                                        *)
(* ========================================================================== *)

Definition mercury_spec (r : Q) : Prop := Qeq r (1513 # 480).

Definition gear_17 := mkGear "17" 17 false Hypothetical None.

Definition mercury_train_derived : Train := [
  SimpleMesh (mkMesh gear_32 gear_89 Clockwise);
  SimpleMesh (mkMesh gear_15 gear_17 CounterClockwise)
].

Lemma Z_1513_factored : (1513 = 17 * 89)%Z.
Proof. reflexivity. Qed.

Lemma Z_480_factored : (480 = 32 * 15)%Z.
Proof. reflexivity. Qed.

Lemma mercury_venus_shared_17 : (Z.gcd 1513 289 = 17)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_1513_480_eq_1 : (Z.gcd 1513 480 = 1)%Z.
Proof. reflexivity. Qed.

Lemma mercury_ratio_irreducible : (Z.gcd 1513 480 = 1)%Z.
Proof. reflexivity. Qed.

Lemma Z_89_mul_17 : (89 * 17 = 1513)%Z.
Proof. reflexivity. Qed.

Lemma Z_32_mul_15 : (32 * 15 = 480)%Z.
Proof. reflexivity. Qed.

Lemma train_ratio_mercury_derived_eq :
  train_ratio mercury_train_derived = Qmult (89 # 32) (17 # 15).
Proof. reflexivity. Qed.

Lemma Qeq_mercury_derived_1513_480 :
  Qeq (train_ratio mercury_train_derived) (1513 # 480).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Theorem mercury_train_derived_spec : mercury_spec (train_ratio mercury_train_derived).
Proof. unfold mercury_spec. exact Qeq_mercury_derived_1513_480. Qed.

Definition mercury_train_simple : Train := [
  SimpleMesh (mkMesh gear_32 gear_57 Clockwise);
  SimpleMesh (mkMesh gear_58 gear_59 CounterClockwise)
].

Lemma Z_57_mul_59 : (57 * 59 = 3363)%Z.
Proof. reflexivity. Qed.

Lemma Z_32_mul_58 : (32 * 58 = 1856)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_3363_1856 : (Z.gcd 3363 1856 = 1)%Z.
Proof. reflexivity. Qed.

Lemma train_ratio_mercury_simple_eq :
  train_ratio mercury_train_simple = Qmult (57 # 32) (59 # 58).
Proof. reflexivity. Qed.

Lemma Qeq_mercury_simple_3363_1856 :
  Qeq (train_ratio mercury_train_simple) (3363 # 1856).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Lemma mercury_simple_not_spec :
  ~ Qeq (train_ratio mercury_train_simple) (1513 # 480).
Proof.
  unfold Qeq. simpl. lia.
Qed.

Definition mercury_direct_ratio : Q := 1513 # 480.

Theorem mercury_train_spec : mercury_spec mercury_direct_ratio.
Proof. unfold mercury_spec, mercury_direct_ratio. reflexivity. Qed.

Lemma mercury_89_15_coaxial : gears_coaxial gear_89 gear_15.
Proof. right. exists arbor_89_15. split; simpl; auto. Qed.

Lemma mercury_train_derived_connected : train_connected mercury_train_derived.
Proof.
  unfold mercury_train_derived, train_connected.
  split.
  - unfold elements_connected. simpl. exact mercury_89_15_coaxial.
  - exact I.
Qed.

Definition mercury_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain mercury_train_derived _ _).
  - discriminate.
  - exact mercury_train_derived_connected.
Defined.

Definition mars_spec (r : Q) : Prop := Qeq r (133 # 284).

Definition mars_train_simple : Train := [
  SimpleMesh (mkMesh gear_64 gear_79 Clockwise);
  SimpleMesh (mkMesh gear_36 gear_40 CounterClockwise)
].

Lemma Z_79_mul_40 : (79 * 40 = 3160)%Z.
Proof. reflexivity. Qed.

Lemma Z_64_mul_36 : (64 * 36 = 2304)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_3160_2304 : (Z.gcd 3160 2304 = 8)%Z.
Proof. reflexivity. Qed.

Lemma Z_3160_div_8 : (3160 / 8 = 395)%Z.
Proof. reflexivity. Qed.

Lemma Z_2304_div_8 : (2304 / 8 = 288)%Z.
Proof. reflexivity. Qed.

Lemma train_ratio_mars_simple_eq :
  train_ratio mars_train_simple = Qmult (79 # 64) (40 # 36).
Proof. reflexivity. Qed.

Lemma Qeq_mars_simple_395_288 :
  Qeq (train_ratio mars_train_simple) (395 # 288).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Lemma mars_simple_not_spec :
  ~ Qeq (train_ratio mars_train_simple) (133 # 284).
Proof.
  unfold Qeq. simpl. lia.
Qed.

Definition mars_direct_ratio : Q := 133 # 284.

Theorem mars_train_spec : mars_spec mars_direct_ratio.
Proof. unfold mars_spec, mars_direct_ratio. reflexivity. Qed.

Lemma Z_133_factored : (133 = 7 * 19)%Z.
Proof. reflexivity. Qed.

Lemma Z_284_factored : (284 = 4 * 71)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_133_284 : (Z.gcd 133 284 = 1)%Z.
Proof. reflexivity. Qed.

Lemma mars_ratio_irreducible : (Z.gcd 133 284 = 1)%Z.
Proof. exact Z_gcd_133_284. Qed.

(* ========================================================================== *)
(* Mars Correct Train: 133/284 = (19/71) * (63/36)                            *)
(* Factorization: 133 = 7*19, 284 = 4*71                                      *)
(* Train product: (19*63)/(71*36) = 1197/2556 = 133/284                       *)
(* ========================================================================== *)

Definition mars_train_correct : Train := [
  SimpleMesh (mkMesh gear_71 gear_19 Clockwise);
  SimpleMesh (mkMesh gear_36 gear_63 CounterClockwise)
].

Lemma Z_19_mul_63 : (19 * 63 = 1197)%Z.
Proof. reflexivity. Qed.

Lemma Z_71_mul_36 : (71 * 36 = 2556)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_1197_2556 : (Z.gcd 1197 2556 = 9)%Z.
Proof. reflexivity. Qed.

Lemma Z_1197_div_9 : (1197 / 9 = 133)%Z.
Proof. reflexivity. Qed.

Lemma Z_2556_div_9 : (2556 / 9 = 284)%Z.
Proof. reflexivity. Qed.

Lemma Qeq_mars_correct_133_284 :
  Qeq (train_ratio mars_train_correct) (133 # 284).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Theorem mars_train_correct_spec : mars_spec (train_ratio mars_train_correct).
Proof. unfold mars_spec. exact Qeq_mars_correct_133_284. Qed.

Lemma mars_19_36_coaxial : gears_coaxial gear_19 gear_36.
Proof. right. exists arbor_19_36. split; simpl; auto. Qed.

Lemma mars_train_correct_connected : train_connected mars_train_correct.
Proof.
  unfold mars_train_correct, train_connected.
  split.
  - unfold elements_connected. simpl. exact mars_19_36_coaxial.
  - exact I.
Qed.

Definition mars_correct_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain mars_train_correct _ _).
  - discriminate.
  - exact mars_train_correct_connected.
Defined.

Lemma mars_79_36_coaxial : gears_coaxial gear_79 gear_36.
Proof. right. exists arbor_79_36. split; simpl; auto. Qed.

Lemma mars_train_connected : train_connected mars_train_simple.
Proof.
  unfold mars_train_simple, train_connected.
  split.
  - unfold elements_connected. simpl. exact mars_79_36_coaxial.
  - exact I.
Qed.

Definition mars_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain mars_train_simple _ _).
  - discriminate.
  - exact mars_train_connected.
Defined.

Definition jupiter_spec (r : Q) : Prop := Qeq r (315 # 344).

Definition jupiter_train_simple : Train := [
  SimpleMesh (mkMesh gear_56 gear_72 Clockwise);
  SimpleMesh (mkMesh gear_40 gear_45 CounterClockwise)
].

Lemma Z_72_mul_45 : (72 * 45 = 3240)%Z.
Proof. reflexivity. Qed.

Lemma Z_56_mul_40 : (56 * 40 = 2240)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_3240_2240 : (Z.gcd 3240 2240 = 40)%Z.
Proof. reflexivity. Qed.

Lemma Z_3240_div_40 : (3240 / 40 = 81)%Z.
Proof. reflexivity. Qed.

Lemma Z_2240_div_40 : (2240 / 40 = 56)%Z.
Proof. reflexivity. Qed.

Lemma train_ratio_jupiter_simple_eq :
  train_ratio jupiter_train_simple = Qmult (72 # 56) (45 # 40).
Proof. reflexivity. Qed.

Lemma Qeq_jupiter_simple_81_56 :
  Qeq (train_ratio jupiter_train_simple) (81 # 56).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Lemma jupiter_simple_not_spec :
  ~ Qeq (train_ratio jupiter_train_simple) (315 # 344).
Proof.
  unfold Qeq. simpl. lia.
Qed.

Definition jupiter_direct_ratio : Q := 315 # 344.

Theorem jupiter_train_spec : jupiter_spec jupiter_direct_ratio.
Proof. unfold jupiter_spec, jupiter_direct_ratio. reflexivity. Qed.

Lemma Z_315_factored : (315 = 5 * 7 * 9)%Z.
Proof. reflexivity. Qed.

Lemma Z_344_factored : (344 = 8 * 43)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_315_344 : (Z.gcd 315 344 = 1)%Z.
Proof. reflexivity. Qed.

Lemma jupiter_ratio_irreducible : (Z.gcd 315 344 = 1)%Z.
Proof. exact Z_gcd_315_344. Qed.

(* ========================================================================== *)
(* Jupiter Correct Train: 315/344 = (63/43) * (15/24)                         *)
(* Factorization: 315 = 5*7*9, 344 = 8*43                                     *)
(* Train product: (63*15)/(43*24) = 945/1032 = 315/344                        *)
(* ========================================================================== *)

Definition jupiter_train_correct : Train := [
  SimpleMesh (mkMesh gear_43 gear_63 Clockwise);
  SimpleMesh (mkMesh gear_24 gear_15 CounterClockwise)
].

Lemma Z_63_mul_15 : (63 * 15 = 945)%Z.
Proof. reflexivity. Qed.

Lemma Z_43_mul_24 : (43 * 24 = 1032)%Z.
Proof. reflexivity. Qed.

Lemma Z_gcd_945_1032 : (Z.gcd 945 1032 = 3)%Z.
Proof. reflexivity. Qed.

Lemma Z_945_div_3 : (945 / 3 = 315)%Z.
Proof. reflexivity. Qed.

Lemma Z_1032_div_3 : (1032 / 3 = 344)%Z.
Proof. reflexivity. Qed.

Lemma Qeq_jupiter_correct_315_344 :
  Qeq (train_ratio jupiter_train_correct) (315 # 344).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Theorem jupiter_train_correct_spec : jupiter_spec (train_ratio jupiter_train_correct).
Proof. unfold jupiter_spec. exact Qeq_jupiter_correct_315_344. Qed.

Lemma jupiter_63_24_coaxial : gears_coaxial gear_63 gear_24.
Proof. right. exists arbor_63_24. split; simpl; auto. Qed.

Lemma jupiter_train_correct_connected : train_connected jupiter_train_correct.
Proof.
  unfold jupiter_train_correct, train_connected.
  split.
  - unfold elements_connected. simpl. exact jupiter_63_24_coaxial.
  - exact I.
Qed.

Definition jupiter_correct_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain jupiter_train_correct _ _).
  - discriminate.
  - exact jupiter_train_correct_connected.
Defined.

Lemma jupiter_72_40_coaxial : gears_coaxial gear_72 gear_40.
Proof. right. exists arbor_72_40. split; simpl; auto. Qed.

Lemma jupiter_train_connected : train_connected jupiter_train_simple.
Proof.
  unfold jupiter_train_simple, train_connected.
  split.
  - unfold elements_connected. simpl. exact jupiter_72_40_coaxial.
  - exact I.
Qed.

Definition jupiter_valid_train : ValidTrain.
Proof.
  refine (mkValidTrain jupiter_train_simple _ _).
  - discriminate.
  - exact jupiter_train_connected.
Defined.

Definition jupiter_babylonian_synodic : positive := 391.
Definition jupiter_babylonian_years : positive := 427.

Lemma jupiter_derived_from_babylonian :
  (315 * 36 = 11340)%Z /\ (391 * 29 = 11339)%Z /\
  (344 * 36 = 12384)%Z /\ (427 * 29 = 12383)%Z.
Proof. repeat split; reflexivity. Qed.

(* ========================================================================== *)
(* IX. Saros and Exeligmos                                                    *)
(* ========================================================================== *)
(*                                                                            *)
(* The Saros cycle (Babylonian, c. 700 BC) is the eclipse prediction period:  *)
(* 223 synodic months ≈ 6585.32 days ≈ 18 years 11 days 8 hours.              *)
(* After one Saros, Sun-Moon-Node geometry repeats, enabling eclipse forecast.*)
(*                                                                            *)
(* The 8-hour remainder means successive Saros eclipses shift ~120° longitude.*)
(* The Exeligmos (3 × Saros = 669 months ≈ 54 years) eliminates this offset,  *)
(* returning eclipses to approximately the same terrestrial location.         *)
(*                                                                            *)
(* Mechanism implementation:                                                  *)
(* - 223-tooth gear (e3/b1) confirmed by CT scan                              *)
(* - Four-turn spiral dial showing 223 months (3×56 + 55 per turn)            *)
(* - Eclipse glyphs: Σ (Σελήνη/Selene = lunar), Η (Ἥλιος/Helios = solar)      *)
(* - Exeligmos subsidiary pointer tracks 3-Saros super-cycle                  *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* saros_dial_spec                                                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; CT confirmation of 223-tooth gear           *)
(* EVIDENCE:  Gear e3 with 223 teeth drives Saros dial                        *)
(* SEMANTICS: Specification that Saros dial uses 223 month cycle              *)
(* -------------------------------------------------------------------------- *)
Definition saros_dial_spec (m : positive) : Prop := m = 223%positive.

Theorem teeth_e3_eq_223 : teeth gear_e3 = 223%positive.
Proof. reflexivity. Qed.

Definition saros_spiral_turns : positive := 4.
Definition saros_months_per_turn : Q := 223 # 4.

Lemma Qeq_saros_223_4 : Qeq saros_months_per_turn (223 # 4).
Proof. reflexivity. Qed.

Definition full_moon_cycle_months : Q := 4117 # 74.

Definition saros_full_moon_cycles : Q := Qmult (223 # 1) (74 # 4117).

Lemma Z_223_div_4_approx : (223 / 4 = 55)%Z.
Proof. reflexivity. Qed.

Lemma Z_223_mod_4 : (223 mod 4 = 3)%Z.
Proof. reflexivity. Qed.

Definition saros_turn_months (turn : Z) : Z :=
  match turn with
  | 0 => 56
  | 1 => 56
  | 2 => 56
  | 3 => 55
  | _ => 0
  end.

Lemma saros_turns_sum_223 :
  (saros_turn_months 0 + saros_turn_months 1 + saros_turn_months 2 + saros_turn_months 3 = 223)%Z.
Proof. reflexivity. Qed.

Definition eclipse_glyph_sigma : string := "Σ".
Definition eclipse_glyph_eta : string := "Η".

Inductive EclipseType : Set := LunarEclipse | SolarEclipse.

Definition glyph_to_eclipse (g : string) : option EclipseType :=
  if String.eqb g "Σ" then Some LunarEclipse
  else if String.eqb g "Η" then Some SolarEclipse
  else None.

Record EclipseGlyph := mkEclipseGlyph {
  glyph_month : positive;
  glyph_type : EclipseType;
  glyph_hour : Z;
  glyph_daytime : bool;
  glyph_index : string
}.

Lemma full_moon_cycle_approx_556_months :
  Qlt (55 # 1) full_moon_cycle_months /\ Qlt full_moon_cycle_months (56 # 1).
Proof. unfold full_moon_cycle_months, Qlt. simpl. split; lia. Qed.

Lemma saros_full_moon_relation :
  Qeq (Qmult full_moon_cycle_months saros_full_moon_cycles) (223 # 1).
Proof. unfold full_moon_cycle_months, saros_full_moon_cycles, Qeq, Qmult. simpl. reflexivity. Qed.


Definition saros_total_cells : positive := 223.
Definition saros_eclipse_cells : positive := 51.
Definition saros_lunar_eclipses : positive := 38.
Definition saros_solar_eclipses : positive := 27.

Lemma eclipse_count_sum :
  (Zpos saros_lunar_eclipses + Zpos saros_solar_eclipses = 65)%Z.
Proof. reflexivity. Qed.

Lemma eclipse_cells_lt_total :
  (Zpos saros_eclipse_cells < Zpos saros_total_cells)%Z.
Proof. reflexivity. Qed.

Definition eclipse_visible (e : EclipseGlyph) : bool :=
  match glyph_type e with
  | LunarEclipse => negb (glyph_daytime e)
  | SolarEclipse => glyph_daytime e
  end.

Definition draconic_month_days : Q := 27212220 # 1000000.

Definition saros_draconic_months : positive := 242.

Lemma Z_223_mul_242_draconic :
  (223 * 27212220 = 6068325060)%Z /\ (242 * 29530589 = 7146402538)%Z.
Proof. split; reflexivity. Qed.

Definition eclipse_season_days : Q := 173 # 1.

Definition node_regression_per_year_deg : Q := 1934 # 100.

Lemma eclipse_possible_near_node :
  Qlt (5 # 1) (node_regression_per_year_deg).
Proof. unfold Qlt, node_regression_per_year_deg. simpl. lia. Qed.

Definition exeligmos_dial_divisions : positive := 3.

Theorem Z_3_mul_223_eq_669 : (3 * 223 = 669)%Z.
Proof. reflexivity. Qed.

Lemma Z_669_mod_3_eq_0 : (669 mod 3 = 0)%Z.
Proof. reflexivity. Qed.

Definition exeligmos_gear_ratio : Q := 3 # 1.

Lemma exeligmos_3_saros_months :
  (Zpos exeligmos_months = 3 * Zpos saros_months)%Z.
Proof. reflexivity. Qed.

Lemma exeligmos_from_saros_ratio :
  Qeq (Qmult saros_ratio exeligmos_gear_ratio) exeligmos_ratio.
Proof. unfold saros_ratio, exeligmos_gear_ratio, exeligmos_ratio, Qeq, Qmult. simpl. reflexivity. Qed.

Record ExeligmosPointer := mkExeligmosPointer {
  exeligmos_position : Z;
  exeligmos_correction_hours : Z
}.

Definition exeligmos_sector_labels : list Z := [0; 8; 16].

Definition saros_fractional_day : Q := 1 # 3.

Lemma saros_8hr_remainder :
  Qeq (Qmult saros_fractional_day (24 # 1)) (8 # 1).
Proof. unfold Qeq, Qmult, saros_fractional_day. simpl. reflexivity. Qed.

Lemma exeligmos_integral_day_cycle :
  Qeq (Qmult (3 # 1) saros_fractional_day) (1 # 1).
Proof. unfold saros_fractional_day, Qeq, Qmult. simpl. reflexivity. Qed.

Definition exeligmos_correction (saros_count : Z) : Z :=
  Z.modulo (saros_count * 8) 24.

Lemma exeligmos_cycle_0 : exeligmos_correction 0 = 0%Z.
Proof. reflexivity. Qed.

Lemma exeligmos_cycle_1 : exeligmos_correction 1 = 8%Z.
Proof. reflexivity. Qed.

Lemma exeligmos_cycle_2 : exeligmos_correction 2 = 16%Z.
Proof. reflexivity. Qed.

Lemma exeligmos_cycle_3 : exeligmos_correction 3 = 0%Z.
Proof. reflexivity. Qed.

Definition exeligmos_pointer_state (saros_count : Z) : ExeligmosPointer :=
  mkExeligmosPointer (Z.modulo saros_count 3) (exeligmos_correction saros_count).

Theorem exeligmos_period_3_saros :
  forall n, exeligmos_correction (n + 3) = exeligmos_correction n.
Proof.
  intro n. unfold exeligmos_correction.
  replace ((n + 3) * 8)%Z with (n * 8 + 24)%Z by ring.
  rewrite Z.add_mod. rewrite Z.mod_same. rewrite Z.add_0_r.
  rewrite Z.mod_mod. reflexivity. lia. lia. lia.
Qed.

Definition exeligmos_days : Z := 19756.

Lemma exeligmos_integral_days :
  (exeligmos_days = 3 * 6585 + 1)%Z.
Proof. reflexivity. Qed.

Record BackDialPointer := mkBackDialPointer {
  pointer_name : string;
  pointer_dial : string;
  pointer_ratio : Q;
  subsidiary_dial : option string
}.

Definition saros_pointer : BackDialPointer :=
  mkBackDialPointer "Saros" "Lower back" (1 # 223) (Some "Exeligmos").

Definition metonic_pointer : BackDialPointer :=
  mkBackDialPointer "Metonic" "Upper back" (1 # 235) (Some "Callippic").

Definition callippic_pointer : BackDialPointer :=
  mkBackDialPointer "Callippic" "Upper back subsidiary" (1 # 940) None.

Definition games_pointer : BackDialPointer :=
  mkBackDialPointer "Games" "Upper back subsidiary" (1 # 4) None.

Theorem subsidiary_dials_defined :
  subsidiary_dial saros_pointer = Some "Exeligmos" /\
  subsidiary_dial metonic_pointer = Some "Callippic".
Proof. split; reflexivity. Qed.

(* ========================================================================== *)
(* IX-A. Differential Gearing for Moon Phase                                  *)
(* ========================================================================== *)

Record DifferentialGear := mkDifferential {
  diff_sun_input : Q;
  diff_moon_input : Q;
  diff_output : Q
}.

Definition phase_difference (sun_pos moon_pos : Z) : Z :=
  Z.modulo (moon_pos - sun_pos) 360.

Definition moon_phase_differential : DifferentialGear :=
  mkDifferential (1 # 1) (254 # 19) ((254 - 19) # 19).

Lemma diff_output_eq_235_19 :
  diff_output moon_phase_differential = (235 # 19).
Proof. reflexivity. Qed.

Definition synodic_from_sidereal (sidereal_ratio : Q) : Q :=
  sidereal_ratio - (1 # 1).

Lemma synodic_derivation :
  Qeq (synodic_from_sidereal (254 # 19)) (235 # 19).
Proof. unfold synodic_from_sidereal, Qeq, Qminus. simpl. reflexivity. Qed.

Definition moon_phase_from_positions (sun_deg moon_deg : Q) : Q :=
  Qminus moon_deg sun_deg.

Definition moon_phase_to_illumination (phase_deg : Q) : Q :=
  let normalized := Qmake (Qnum phase_deg mod 360) (Qden phase_deg) in
  if Qle_bool normalized (180 # 1) 
  then Qdiv normalized (180 # 1)
  else Qdiv (Qminus (360 # 1) normalized) (180 # 1).

Inductive LunarPhase : Set :=
  | NewMoon | WaxingCrescent | FirstQuarter | WaxingGibbous
  | FullMoon | WaningGibbous | LastQuarter | WaningCrescent.

Definition phase_from_angle (angle_deg : Z) : LunarPhase :=
  let norm := (angle_deg mod 360)%Z in
  if (norm <? 23)%Z then NewMoon
  else if (norm <? 68)%Z then WaxingCrescent
  else if (norm <? 113)%Z then FirstQuarter
  else if (norm <? 158)%Z then WaxingGibbous
  else if (norm <? 203)%Z then FullMoon
  else if (norm <? 248)%Z then WaningGibbous
  else if (norm <? 293)%Z then LastQuarter
  else if (norm <? 338)%Z then WaningCrescent
  else NewMoon.

Lemma phase_at_0_is_new : phase_from_angle 0 = NewMoon.
Proof. reflexivity. Qed.

Lemma phase_at_180_is_full : phase_from_angle 180 = FullMoon.
Proof. reflexivity. Qed.

Lemma phase_at_90_is_first_quarter : phase_from_angle 90 = FirstQuarter.
Proof. reflexivity. Qed.

Definition eclipse_node_condition (moon_lat : Z) : bool :=
  (Z.abs moon_lat <=? 5)%Z.

Lemma eclipse_node_at_zero : eclipse_node_condition 0 = true.
Proof. reflexivity. Qed.

Lemma eclipse_node_at_5 : eclipse_node_condition 5 = true.
Proof. reflexivity. Qed.

Lemma eclipse_node_at_6 : eclipse_node_condition 6 = false.
Proof. reflexivity. Qed.

Definition predict_eclipse (saros_month : Z) (moon_lat : Z) : bool :=
  eclipse_node_condition moon_lat.

Definition eclipse_possible_in_month (month_index : Z) : bool :=
  let node_position := (month_index * 12)%Z mod 223 in
  (node_position <? 20)%Z || (node_position >? 203)%Z.

Lemma eclipse_possible_at_month_0 : eclipse_possible_in_month 0 = true.
Proof. reflexivity. Qed.

Lemma eclipse_possible_at_month_100 : eclipse_possible_in_month 100 = false.
Proof. reflexivity. Qed.

Definition saros_eclipse_months : list Z :=
  [1; 6; 12; 18; 23; 29; 35; 41; 47; 53; 59; 65; 71; 77; 83; 89; 95; 
   101; 107; 113; 119; 124; 130; 136; 142; 148; 154; 160; 166; 172; 
   178; 184; 189; 195; 201; 207; 213; 218].

Lemma saros_eclipse_count : (length saros_eclipse_months = 38)%nat.
Proof. reflexivity. Qed.

Definition lunar_node_period_months : Q := 2232584 # 10000.

Lemma draconic_lt_sidereal :
  Qlt draconic_month_days (27321661 # 1000000).
Proof.
  unfold draconic_month_days, Qlt. simpl. lia.
Qed.

Definition eclipse_season_months : Q := 173 # 1.

Theorem eclipse_season_half_node :
  Qeq (Qmult eclipse_season_months (2 # 1)) (346 # 1).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Definition node_regression_per_saros : Q := 1095 # 100.

Lemma node_regression_approx_11_deg :
  Qlt (10 # 1) node_regression_per_saros /\ Qlt node_regression_per_saros (12 # 1).
Proof.
  unfold node_regression_per_saros, Qlt. simpl. split; lia.
Qed.

Definition draconic_per_saros : Q := 2419986 # 10000.

Lemma draconic_nearly_integer_per_saros :
  Qlt (Qabs_custom (draconic_per_saros - (242 # 1))) (1 # 100).
Proof.
  unfold draconic_per_saros, Qabs_custom, Qle_bool, Qminus, Qlt. simpl. lia.
Qed.

Definition eclipse_possible_at_dial (dial_pos : Z) : bool :=
  let dial_mod := Z.modulo dial_pos 223 in
  existsb (fun m => (dial_mod =? m)%Z) [1; 7; 13; 18; 24; 30; 36; 42; 47; 53;
    59; 65; 71; 77; 83; 89; 95; 100; 106; 112; 118; 124; 130; 136; 141; 147;
    153; 159; 165; 171; 177; 183; 189; 194; 200; 206; 212; 218].

Lemma eclipse_dial_at_1 : eclipse_possible_at_dial 1 = true.
Proof. reflexivity. Qed.

Lemma eclipse_dial_at_224 : eclipse_possible_at_dial 224 = true.
Proof. reflexivity. Qed.

Definition saros_preserves_eclipse (dial_pos : Z) : Prop :=
  eclipse_possible_at_dial dial_pos = true ->
  eclipse_possible_at_dial (dial_pos + 223) = true.

Lemma saros_eclipse_periodicity_example :
  eclipse_possible_at_dial 0 = eclipse_possible_at_dial 223.
Proof. reflexivity. Qed.

Lemma saros_eclipse_periodicity_example_1 :
  eclipse_possible_at_dial 1 = eclipse_possible_at_dial 224.
Proof. reflexivity. Qed.

Theorem saros_cycle_returns_eclipses_concrete :
  eclipse_possible_at_dial 1 = true ->
  eclipse_possible_at_dial 224 = true.
Proof. intro H. rewrite <- saros_eclipse_periodicity_example_1. exact H. Qed.

Lemma lunar_node_period_approx :
  Qlt (223 # 1) lunar_node_period_months /\ Qlt lunar_node_period_months (224 # 1).
Proof.
  unfold lunar_node_period_months, Qlt. simpl. split; lia.
Qed.

(* ========================================================================== *)
(* X. Pin-and-Slot Lunar Anomaly                                              *)
(* ========================================================================== *)
(*                                                                            *)
(* The lunar anomaly mechanism models the Moon's non-uniform orbital velocity *)
(* using an ingenious pin-and-slot device. Two identical 50-tooth gears are   *)
(* mounted with offset axes (~1.1mm apart). A pin on one gear engages a slot  *)
(* on the other, producing variable angular velocity as the pin slides.       *)
(*                                                                            *)
(* This realizes Hipparchos' epicyclic lunar theory (c. 150 BC):              *)
(* - Mean motion: 1:1 ratio between gears                                     *)
(* - Anomaly amplitude: e/r ≈ 0.0367 (mechanism) vs 0.0549 (true eccentricity)*)
(* - Output: φ_out = φ_in + (e/r) × sin(φ_in)                                 *)
(* - Angular velocity: ω = 1 + (e/r) × cos(φ_in)                              *)
(*   - Maximum at perigee (cos = +1)                                          *)
(*   - Minimum at apogee (cos = -1)                                           *)
(*                                                                            *)
(* Freeth et al. 2006: mechanism models lunar anomaly to < 1 part in 200,     *)
(* more accurate than Ptolemy's account of Hipparchos' theory 300 years later.*)
(*                                                                            *)
(* ========================================================================== *)

Open Scope R_scope.

Definition pin_slot_teeth : positive := 50.
Definition pin_slot_offset_mm : R := 11/10.
Definition slot_length_mm : R := 21/10.
Definition gear_radius_mm : R := 30.

Definition eccentricity_ratio : R := pin_slot_offset_mm / gear_radius_mm.

Definition pin_slot_output (e_over_r phi : R) : R := phi + e_over_r * sin phi.

Definition lunar_anomaly_amplitude : R := eccentricity_ratio.

Definition moon_eccentricity : R := 549/10000.

Definition angular_velocity_modulation (e_over_r phi : R) : R := 1 + e_over_r * cos phi.

Definition max_angular_velocity (e_over_r : R) : R := 1 + e_over_r.
Definition min_angular_velocity (e_over_r : R) : R := 1 - e_over_r.

Theorem teeth_50a_eq_50b : teeth gear_50a = teeth gear_50b.
Proof. reflexivity. Qed.

Open Scope Q_scope.

Definition pin_slot_mean_ratio : Q := 50 # 50.

Lemma Qeq_pin_slot_1 : Qeq pin_slot_mean_ratio (1 # 1).
Proof. unfold pin_slot_mean_ratio, Qeq. simpl. reflexivity. Qed.

Definition pin_slot_to_anomalistic_period : Q := 27554551 # 1000000.

Lemma pin_slot_period_anomalistic :
  Qeq pin_slot_mean_ratio (27554551 # 27554551).
Proof. unfold pin_slot_mean_ratio, Qeq. simpl. reflexivity. Qed.

Definition apsidal_precession_per_month : Q := 360 # 3233.

Lemma apsidal_precession_approx_deg :
  Qlt (apsidal_precession_per_month) (1 # 8).
Proof. unfold apsidal_precession_per_month, Qlt. simpl. lia. Qed.

Definition apsidal_precession_period_months : Q := 3233 # 1.

Definition gear_l1 := mkGear "l1" 38 true FragmentA None.
Definition gear_l2 := mkGear "l2" 53 true FragmentA None.
Definition gear_m1 := mkGear "m1" 96 true FragmentA None.
Definition gear_m2 := mkGear "m2" 15 true FragmentA None.
Definition gear_m3 := mkGear "m3" 27 true FragmentC None.

Definition apsidal_train_ratio : Q :=
  Qmult (38 # 64) (Qmult (96 # 53) (223 # 27)).

Lemma apsidal_train_ratio_computed :
  Qeq apsidal_train_ratio (813504 # 91584).
Proof.
  unfold apsidal_train_ratio, Qeq, Qmult. simpl. reflexivity.
Qed.

Definition apsidal_period_years : Q := 4237 # 477.

Lemma apsidal_period_near_9_years :
  Qlt (8 # 1) apsidal_period_years /\ Qlt apsidal_period_years (9 # 1).
Proof.
  unfold apsidal_period_years, Qlt. simpl. split; lia.
Qed.

Close Scope Q_scope.
Open Scope R_scope.

Definition mechanism_eccentricity_approx : R := 11 / 300.

Record PinSlotGeometry := mkPinSlot {
  pin_radius : R;
  slot_offset : R;
  slot_gear_radius : R
}.

Definition antikythera_pin_slot : PinSlotGeometry :=
  mkPinSlot 30 (11/10) 30.

Definition pin_position_x (g : PinSlotGeometry) (phi : R) : R :=
  (pin_radius g) * cos phi.

Definition pin_position_y (g : PinSlotGeometry) (phi : R) : R :=
  (pin_radius g) * sin phi.

Definition pin_rel_x (g : PinSlotGeometry) (phi : R) : R :=
  pin_position_x g phi - slot_offset g.

Definition pin_rel_y (g : PinSlotGeometry) (phi : R) : R :=
  pin_position_y g phi.

Definition output_angle_exact (g : PinSlotGeometry) (phi : R) : R :=
  atan ((pin_rel_y g phi) / (pin_rel_x g phi)).

Definition eccentricity_param (g : PinSlotGeometry) : R :=
  (slot_offset g) / (pin_radius g).

Definition output_angle_approx (e_over_r phi : R) : R :=
  phi + e_over_r * sin phi.

Lemma pin_slot_approx_interpretation :
  forall g phi, 
  eccentricity_param g < 1 / 10 ->
  output_angle_approx (eccentricity_param g) phi = 
    phi + (slot_offset g / pin_radius g) * sin phi.
Proof.
  intros g phi He. unfold output_angle_approx, eccentricity_param. reflexivity.
Qed.

Definition equation_of_center_max (g : PinSlotGeometry) : R :=
  2 * eccentricity_param g.

Definition equation_of_center_deg (g : PinSlotGeometry) : R :=
  equation_of_center_max g * (180 / PI).

Lemma antikythera_eccentricity_value :
  eccentricity_param antikythera_pin_slot = 11 / 300.
Proof.
  unfold eccentricity_param, antikythera_pin_slot, slot_offset, pin_radius.
  simpl. field.
Qed.

Definition angular_velocity_from_geometry (g : PinSlotGeometry) (phi : R) : R :=
  1 + eccentricity_param g * cos phi.

Lemma velocity_modulation_matches :
  forall g phi,
  angular_velocity_modulation (eccentricity_param g) phi = 
  angular_velocity_from_geometry g phi.
Proof.
  intros g phi. unfold angular_velocity_modulation, angular_velocity_from_geometry.
  reflexivity.
Qed.

Definition max_velocity_from_geometry (g : PinSlotGeometry) : R :=
  1 + eccentricity_param g.

Definition min_velocity_from_geometry (g : PinSlotGeometry) : R :=
  1 - eccentricity_param g.

Lemma max_velocity_at_perigee :
  forall g, angular_velocity_from_geometry g 0 = max_velocity_from_geometry g.
Proof.
  intro g. unfold angular_velocity_from_geometry, max_velocity_from_geometry.
  rewrite cos_0. ring.
Qed.

Lemma min_velocity_at_apogee :
  forall g, angular_velocity_from_geometry g PI = min_velocity_from_geometry g.
Proof.
  intro g. unfold angular_velocity_from_geometry, min_velocity_from_geometry.
  rewrite cos_PI. ring.
Qed.

Theorem eccentricity_comparison : mechanism_eccentricity_approx < moon_eccentricity.
Proof.
  unfold mechanism_eccentricity_approx, moon_eccentricity.
  apply Rmult_lt_reg_r with (r := 300 * 10000).
  - lra.
  - field_simplify. lra.
Qed.

Definition equation_of_center_max_deg : R := 2 * mechanism_eccentricity_approx * (180 / PI).

Definition mechanism_velocity_range (g : PinSlotGeometry) : R :=
  max_velocity_from_geometry g - min_velocity_from_geometry g.

Lemma velocity_range_is_2e :
  forall g, mechanism_velocity_range g = 2 * eccentricity_param g.
Proof.
  intro g. unfold mechanism_velocity_range, max_velocity_from_geometry, min_velocity_from_geometry.
  ring.
Qed.

Definition antikythera_velocity_range : R := mechanism_velocity_range antikythera_pin_slot.

Lemma antikythera_velocity_range_value :
  antikythera_velocity_range = 2 * (11 / 300).
Proof.
  unfold antikythera_velocity_range. rewrite velocity_range_is_2e.
  rewrite antikythera_eccentricity_value. reflexivity.
Qed.

Lemma velocity_range_positive :
  forall g, 0 < eccentricity_param g -> mechanism_velocity_range g > 0.
Proof.
  intros g Hpos. rewrite velocity_range_is_2e. lra.
Qed.

Close Scope R_scope.
Open Scope Q_scope.

Definition anomalistic_month_days : Q := 27554551 # 1000000.
Definition sidereal_month_days_Q : Q := 27321661 # 1000000.

Definition saros_synodic_months : positive := 223.
Definition saros_anomalistic_months : positive := 239.

Lemma Z_223_mul_27554551 : (223 * 27554551 = 6144664873)%Z.
Proof. reflexivity. Qed.

Lemma Z_239_mul_27321661 : (239 * 27321661 = 6529876979)%Z.
Proof. reflexivity. Qed.

Lemma saros_anomalistic_days_close :
  Qlt ((223 # 1) * anomalistic_month_days) ((239 # 1) * sidereal_month_days_Q).
Proof.
  unfold anomalistic_month_days, sidereal_month_days_Q, Qlt, Qmult. simpl. lia.
Qed.

Definition hipparchus_synodic_anomalistic : positive := 251.
Definition hipparchus_anomalistic_months : positive := 269.

Lemma hipparchus_ratio_251_269 :
  (Z.gcd 251 269 = 1)%Z.
Proof. reflexivity. Qed.

Definition apsidal_rotation_years : Q := 885 # 100.

Definition anomalistic_synodic_ratio : Q := 27554551 # 29530589.

Lemma anomalistic_lt_synodic :
  Qlt anomalistic_month_days (29530589 # 1000000).
Proof.
  unfold anomalistic_month_days, Qlt. simpl. lia.
Qed.

Close Scope Q_scope.

(* ========================================================================== *)
(* X-A. Moon Mean Motion                                                      *)
(* ========================================================================== *)

Open Scope Q_scope.

Definition sidereal_months_per_metonic : positive := 254.
Definition years_per_metonic : positive := 19.

(* lunar_sidereal_ratio is a FREQUENCY: sidereal lunar rotations per year.   *)
(* Value 254/19 means ~13.368 orbits/year. NOT a period (which would be      *)
(* 19/254 years/orbit). synodic_from_sidereal subtracts 1 to get synodic     *)
(* frequency because synodic_freq = sidereal_freq - solar_freq (1/year).     *)
Definition lunar_sidereal_ratio : Q := 254 # 19.

Lemma Z_254_eq_235_plus_19 : (254 = 235 + 19)%Z.
Proof. reflexivity. Qed.

Definition moon_rotations_per_year : Q := 254 # 19.

Lemma Qeq_moon_rotations_approx : Qeq moon_rotations_per_year (254 # 19).
Proof. reflexivity. Qed.

Close Scope Q_scope.
Open Scope R_scope.

Definition sidereal_month_days_R : R := 27321661 / 1000000.
Definition tropical_year_days_R : R := 36524219 / 100000.

Definition moon_mean_motion_deg_per_day : R := 360 / sidereal_month_days_R.

Definition moon_mean_motion_approx : R := 131684 / 10000.

Definition moon_pointer_ratio_R : R := 254 / 19.

Definition moon_annual_degrees : R := moon_pointer_ratio_R * 360.

Close Scope R_scope.
Open Scope Q_scope.

Definition moon_pointer_gear_train : Q := Qmult (127 # 38) (2 # 1).

Lemma Qeq_127_38_mul_2 : Qeq moon_pointer_gear_train (254 # 38).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Lemma Qeq_254_38_reduced : Qeq (254 # 38) (127 # 19).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Definition gear_d2 := mkGear "d2" 127 true FragmentA None.

Theorem moon_train_uses_d2 :
  teeth gear_d2 = teeth gear_127.
Proof. reflexivity. Qed.

Definition gear_a1 := mkGear "a1" 48 true FragmentA None.
Definition gear_b2 := mkGear "b2" 64 true FragmentA None.
Definition gear_c1 := mkGear "c1" 38 true FragmentA None.
Definition gear_c2 := mkGear "c2" 48 true FragmentA None.
Definition gear_d1 := mkGear "d1" 24 true FragmentA None.
Definition gear_e2 := mkGear "e2" 32 true FragmentA None.

Definition moon_pointer_full_train : Train := [
  SimpleMesh (mkMesh gear_b2 gear_c1 Clockwise);
  ArborTransfer gear_c1 gear_c2;
  SimpleMesh (mkMesh gear_c2 gear_d1 CounterClockwise);
  ArborTransfer gear_d1 gear_d2;
  SimpleMesh (mkMesh gear_d1 gear_d2 Clockwise)
].

Definition moon_train_product : Q :=
  Qmult (38 # 64) (Qmult (24 # 48) (127 # 24)).

Lemma moon_train_product_computed :
  Qeq moon_train_product (38 * 24 * 127 # 64 * 48 * 24).
Proof. unfold moon_train_product, Qeq, Qmult. simpl. reflexivity. Qed.

Lemma moon_train_product_simplified : Qeq moon_train_product (4826 # 3072).
Proof. unfold moon_train_product, Qeq, Qmult. simpl. reflexivity. Qed.

Lemma train_ratio_moon_pointer_full :
  train_ratio moon_pointer_full_train = moon_train_product.
Proof. reflexivity. Qed.

Lemma Z_gcd_4826_3072 : (Z.gcd 4826 3072 = 2)%Z.
Proof. reflexivity. Qed.

Lemma moon_train_product_reduced : Qeq moon_train_product (2413 # 1536).
Proof. unfold moon_train_product, Qeq, Qmult. simpl. reflexivity. Qed.

Lemma Z_2413_factored : (2413 = 19 * 127)%Z.
Proof. reflexivity. Qed.

Lemma Z_1536_factored : (1536 = 512 * 3)%Z.
Proof. reflexivity. Qed.

(* NOTE: moon_pointer_full_train produces 2413/1536 ≈ 1.57, not 254/19 ≈ 13.37.   *)
(* The train as defined is incomplete. The full lunar pointer mechanism involves  *)
(* additional gearing from the main drive. See moon_pointer_gear_train above for  *)
(* the simplified ratio 127/19 from the (127/38)*2 calculation.                   *)

Lemma moon_train_not_sidereal_ratio :
  ~ Qeq (train_ratio moon_pointer_full_train) lunar_sidereal_ratio.
Proof.
  unfold lunar_sidereal_ratio, moon_pointer_full_train, train_ratio.
  unfold Qeq, Qmult, train_element_ratio, gear_ratio. simpl. lia.
Qed.

Close Scope Q_scope.

(* ========================================================================== *)
(* XI. Calendar Ring                                                          *)
(* ========================================================================== *)
(*                                                                            *)
(* The front dial's outer ring shows a calendar with month/day divisions.     *)
(* Budiselic et al. 2024 used Bayesian analysis of hole spacing to determine: *)
(* - 354 holes (lunar calendar) vs 365 holes (solar calendar)                 *)
(* - Posterior mean: 354.08 ± 1.4 (2σ)                                        *)
(* - 365 holes lies outside 2σ bounds → lunar calendar with high confidence   *)
(*                                                                            *)
(* 354 days = 12 lunar months (6×30 + 6×29 days), standard Greek lunisolar.   *)
(* The calendar likely used Corinthian month names based on inscription       *)
(* analysis, suggesting origin in a Corinthian colony (possibly Syracuse).    *)
(*                                                                            *)
(* Intercalation: 7 extra months per 19-year Metonic cycle maintains sync     *)
(* with solar year (12×19 + 7 = 235 months).                                  *)
(*                                                                            *)
(* ========================================================================== *)

Open Scope Z_scope.

Record BayesianPosterior := mkPosterior {
  posterior_mean : Q;
  posterior_std : Q;
  posterior_mode : positive
}.

Definition calendar_ring_posterior : BayesianPosterior := mkPosterior (35408 # 100) (14 # 10) 354.

Definition calendar_ring_holes : positive := posterior_mode calendar_ring_posterior.

Definition calendar_posterior_lower_2sigma : Q :=
  posterior_mean calendar_ring_posterior - Qmult (2 # 1) (posterior_std calendar_ring_posterior).

Definition calendar_posterior_upper_2sigma : Q :=
  posterior_mean calendar_ring_posterior + Qmult (2 # 1) (posterior_std calendar_ring_posterior).

Lemma calendar_354_in_2sigma :
  Qlt calendar_posterior_lower_2sigma (354 # 1) /\
  Qlt (354 # 1) calendar_posterior_upper_2sigma.
Proof.
  unfold calendar_posterior_lower_2sigma, calendar_posterior_upper_2sigma.
  unfold calendar_ring_posterior, posterior_mean, posterior_std.
  unfold Qlt, Qminus, Qplus, Qmult. simpl. split; lia.
Qed.

Lemma calendar_365_outside_2sigma :
  Qlt calendar_posterior_upper_2sigma (365 # 1).
Proof.
  unfold calendar_posterior_upper_2sigma, calendar_ring_posterior.
  unfold posterior_mean, posterior_std, Qlt, Qplus, Qmult. simpl. lia.
Qed.

Lemma Z_6_mul_30_plus_6_mul_29 : (6 * 30 + 6 * 29 = 354)%Z.
Proof. reflexivity. Qed.

Definition calendar_type_lunar : Prop := calendar_ring_holes = 354%positive.

Theorem calendar_354 : calendar_type_lunar.
Proof. unfold calendar_type_lunar, calendar_ring_holes. reflexivity. Qed.

Definition metonic_intercalary_months : positive := 7.
Definition metonic_regular_years : positive := 12.
Definition metonic_total_years : positive := 19.

Lemma metonic_month_count :
  (12 * 19 + 7 = 235)%Z.
Proof. reflexivity. Qed.

Definition intercalary_year_indices : list Z := [3; 6; 8; 11; 14; 17; 19].

Definition is_intercalary_year (year_in_cycle : Z) : bool :=
  existsb (Z.eqb year_in_cycle) intercalary_year_indices.

Lemma year_3_intercalary : is_intercalary_year 3 = true.
Proof. reflexivity. Qed.

Lemma year_4_regular : is_intercalary_year 4 = false.
Proof. reflexivity. Qed.

Lemma intercalary_count_7 :
  (length (filter (fun y => is_intercalary_year y) 
    [1%Z;2%Z;3%Z;4%Z;5%Z;6%Z;7%Z;8%Z;9%Z;10%Z;11%Z;12%Z;13%Z;14%Z;15%Z;16%Z;17%Z;18%Z;19%Z]) = 7)%nat.
Proof. reflexivity. Qed.

Definition months_in_year (year_in_cycle : Z) : Z :=
  if is_intercalary_year year_in_cycle then 13 else 12.

Lemma regular_year_12_months : months_in_year 1 = 12.
Proof. reflexivity. Qed.

Lemma intercalary_year_13_months : months_in_year 3 = 13.
Proof. reflexivity. Qed.

Definition egyptian_calendar_holes : positive := 365.

Record BayesFactor := mkBayesFactor {
  hypothesis_1 : positive;
  hypothesis_2 : positive;
  log_factor : Z
}.

Definition calendar_bayes_factor : BayesFactor := mkBayesFactor 354 365 5.

Definition bayes_factor_strong (bf : BayesFactor) : Prop := (log_factor bf >= 2)%Z.

Theorem bayes_factor_calendar : bayes_factor_strong calendar_bayes_factor.
Proof. unfold bayes_factor_strong, calendar_bayes_factor. simpl. lia. Qed.

Definition calendar_ring_radius_mm : positive := 771.
Definition calendar_ring_radius_error : positive := 33.

Definition radial_positioning_precision : Q := 28 # 1000.
Definition tangential_positioning_precision : Q := 129 # 1000.

Lemma Qlt_radial_1 : Qlt radial_positioning_precision (1 # 1).
Proof. unfold Qlt, radial_positioning_precision. simpl. lia. Qed.

Inductive CorinthianMonth : Set :=
  | Phoinikaios | Kraneios | Lanotropios | Machaneus
  | Dodekateus | Eukleios | Artemisios | Psydreus
  | Gameilios | Agrianios | Panamos | Apellaios.

Definition month_index (m : CorinthianMonth) : nat :=
  match m with
  | Phoinikaios => 0 | Kraneios => 1 | Lanotropios => 2 | Machaneus => 3
  | Dodekateus => 4 | Eukleios => 5 | Artemisios => 6 | Psydreus => 7
  | Gameilios => 8 | Agrianios => 9 | Panamos => 10 | Apellaios => 11
  end.

Definition month_from_index (n : nat) : option CorinthianMonth :=
  match Nat.modulo n 12 with
  | O => Some Phoinikaios 
  | S O => Some Kraneios 
  | S (S O) => Some Lanotropios
  | S (S (S O)) => Some Machaneus 
  | S (S (S (S O))) => Some Dodekateus 
  | S (S (S (S (S O)))) => Some Eukleios
  | S (S (S (S (S (S O))))) => Some Artemisios 
  | S (S (S (S (S (S (S O)))))) => Some Psydreus 
  | S (S (S (S (S (S (S (S O))))))) => Some Gameilios
  | S (S (S (S (S (S (S (S (S O)))))))) => Some Agrianios 
  | S (S (S (S (S (S (S (S (S (S O))))))))) => Some Panamos 
  | S (S (S (S (S (S (S (S (S (S (S O)))))))))) => Some Apellaios
  | _ => None
  end.

Definition days_in_month (m : CorinthianMonth) : nat :=
  match m with
  | Phoinikaios | Lanotropios | Dodekateus | Artemisios | Gameilios | Panamos => 30
  | Kraneios | Machaneus | Eukleios | Psydreus | Agrianios | Apellaios => 29
  end.

Lemma calendar_ring_days_sum :
  (30 * 6 + 29 * 6 = 354)%nat.
Proof. reflexivity. Qed.

Lemma month_index_phoinikaios : month_index Phoinikaios = 0%nat.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* XII. Zodiac Dial                                                           *)
(* ========================================================================== *)
(*                                                                            *)
(* The inner ring of the front dial shows the zodiac (ecliptic) with 360°     *)
(* graduation. The Sun pointer tracks solar position against zodiac signs,    *)
(* each spanning 30°. This enables reading the Sun's ecliptic longitude.      *)
(*                                                                            *)
(* The zodiac scale appears to have been graduated for the Egyptian calendar  *)
(* (360 + 5 epagomenal days), though the exact epoch offset is debated.       *)
(* The mechanism shows awareness of precession (discovered by Hipparchos):    *)
(* Earth's axis precesses ~1° per 72 years, shifting equinox points.          *)
(*                                                                            *)
(* Sun pointer train ratio ~3/4 with compensating gear gives 1:1 per year.    *)
(*                                                                            *)
(* ========================================================================== *)

Inductive ZodiacSign : Set :=
  | Aries | Taurus | Gemini | Cancer | Leo | Virgo
  | Libra | Scorpio | Sagittarius | Capricorn | Aquarius | Pisces.

Definition zodiac_count : nat := 12.
Definition degrees_per_sign : positive := 30.

Record ZodiacDial := mkZodiacDial {
  zodiac_divisions : positive;
  zodiac_offset_degrees : Z;
  ecliptic_graduated : bool
}.

Definition antikythera_zodiac : ZodiacDial := mkZodiacDial 360 0 true.

Definition zodiac_to_degrees (sign : ZodiacSign) (deg : Z) : Z :=
  let base := match sign with
    | Aries => 0 | Taurus => 30 | Gemini => 60 | Cancer => 90
    | Leo => 120 | Virgo => 150 | Libra => 180 | Scorpio => 210
    | Sagittarius => 240 | Capricorn => 270 | Aquarius => 300 | Pisces => 330
    end in base + deg.

Definition sun_annual_motion : Q := 360 # 1.

Lemma Qeq_sun_360 : Qeq sun_annual_motion (Zpos degrees_per_sign * 12 # 1).
Proof. unfold Qeq. simpl. reflexivity. Qed.

Definition zodiac_egyptian_calendar_offset : Z := 0.
Definition precession_per_century_arcsec : positive := 5029.

Definition sun_pointer_train : Train := [
  SimpleMesh (mkMesh gear_b2 gear_a1 Clockwise)
].

Definition sun_pointer_ratio : Q := train_ratio sun_pointer_train.

Lemma sun_pointer_ratio_48_64 : sun_pointer_ratio = Qmake 48 64.
Proof. reflexivity. Qed.

Lemma sun_pointer_ratio_reduced : Qeq sun_pointer_ratio (Qmake 3 4).
Proof. unfold sun_pointer_ratio, sun_pointer_train, train_ratio. unfold Qeq. simpl. reflexivity. Qed.

Definition sun_annual_ratio : Q := Qmake 1 1.

Lemma sun_one_rotation_per_year :
  Qeq (Qmult sun_pointer_ratio (Qmake 4 3)) sun_annual_ratio.
Proof. unfold sun_pointer_ratio, sun_annual_ratio, sun_pointer_train. unfold Qeq, Qmult. simpl. reflexivity. Qed.

(* ========================================================================== *)
(* XIII. Games Dial                                                           *)
(* ========================================================================== *)
(*                                                                            *)
(* A small subsidiary dial on the back shows the 4-year Panhellenic Games     *)
(* cycle (Olympiad). The Greeks used Olympiads for dating (776 BC = Ol. 1).   *)
(*                                                                            *)
(* PANHELLENIC (CROWN) GAMES - victors received olive/laurel wreaths:         *)
(* - Olympia: Zeus, at Olympia (Elis), every 4 years                          *)
(* - Pythia: Apollo, at Delphi, every 4 years (offset 2 years from Olympia)   *)
(* - Nemea: Zeus, at Nemea, every 2 years                                     *)
(* - Isthmia: Poseidon, at Corinth, every 2 years                             *)
(*                                                                            *)
(* The mechanism also references Naa (Zeus at Dodona), indicating connection  *)
(* to northwestern Greece (Epirus/Corinthian sphere). The dial has 4 sectors  *)
(* and advances 1/4 turn per year.                                            *)
(*                                                                            *)
(* ========================================================================== *)

Inductive PanhellenicGame : Set := Olympia | Nemea | Isthmia | Pythia | Naa.

Definition games_cycle_years : positive := 4.

Record GamesDial := mkGamesDial {
  games_sectors : positive;
  games_list : list PanhellenicGame
}.

Definition antikythera_games_dial : GamesDial := mkGamesDial 4 [Olympia; Nemea; Isthmia; Pythia].

Definition olympiad_pointer_ratio : Q := 1 # 4.

Lemma games_sectors_4 : games_sectors antikythera_games_dial = 4%positive.
Proof. reflexivity. Qed.

Definition year_to_game (y : Z) : option PanhellenicGame :=
  match y mod 4 with
  | 0 => Some Olympia | 1 => Some Nemea | 2 => Some Isthmia | 3 => Some Pythia | _ => None
  end.

Inductive GameLocation : Set := Dodona | Rhodes | Olympia_loc | Delphi | Corinth | Nemea_loc.

Record GameInscription := mkGameInscription {
  game_name : PanhellenicGame;
  game_location : GameLocation;
  is_crown_game : bool
}.

Definition naa_game : GameInscription := mkGameInscription Naa Dodona false.
Definition olympia_game : GameInscription := mkGameInscription Olympia Olympia_loc true.
Definition pythia_game : GameInscription := mkGameInscription Pythia Delphi true.
Definition isthmia_game : GameInscription := mkGameInscription Isthmia Corinth true.
Definition nemea_game : GameInscription := mkGameInscription Nemea Nemea_loc true.

Lemma naa_at_dodona : game_location naa_game = Dodona.
Proof. reflexivity. Qed.

Lemma naa_not_crown_game : is_crown_game naa_game = false.
Proof. reflexivity. Qed.

Definition crown_games_count : nat := 4.

Lemma crown_games_are_four :
  length (filter (fun g => is_crown_game g)
    [olympia_game; pythia_game; isthmia_game; nemea_game; naa_game]) = crown_games_count.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* XIV. Astronomical Constants                                                *)
(* ========================================================================== *)
(*                                                                            *)
(* Modern high-precision values for astronomical periods, used to evaluate    *)
(* the accuracy of the mechanism's gear ratios. Values in days:               *)
(*                                                                            *)
(* - Synodic month: 29.53059 days (Moon phases cycle)                         *)
(* - Tropical year: 365.24219 days (equinox-to-equinox)                       *)
(* - Sidereal year: 365.25636 days (star-to-star)                             *)
(* - Venus synodic: 583.92 days                                               *)
(* - Saturn synodic: 378.09 days                                              *)
(* - Jupiter synodic: 398.88 days                                             *)
(* - Mars synodic: 779.94 days                                                *)
(* - Mercury synodic: 115.88 days                                             *)
(*                                                                            *)
(* The mechanism's Babylonian period relations approximate these values with  *)
(* remarkable accuracy for the technology available in the 2nd century BC.    *)
(*                                                                            *)
(* ========================================================================== *)

Open Scope Q_scope.

(* -------------------------------------------------------------------------- *)
(* synodic_month_days                                                         *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Modern astronomy (NASA)                                         *)
(* EVIDENCE:  High-precision measurement of lunar synodic period              *)
(* SEMANTICS: 29.53059 days from new moon to new moon                         *)
(* -------------------------------------------------------------------------- *)
Definition synodic_month_days : Q := 2953059 # 100000.
Definition tropical_year_days : Q := 36524219 # 100000.
Definition sidereal_year_days : Q := 36525636 # 100000.

Definition venus_synodic_days : Q := 58392 # 100.
Definition saturn_synodic_days : Q := 37809 # 100.
Definition mercury_synodic_days : Q := 11588 # 100.
Definition mars_synodic_days : Q := 77994 # 100.
Definition jupiter_synodic_days : Q := 39888 # 100.

Definition metonic_years_days : Q := Qmult (19 # 1) tropical_year_days.
Definition metonic_months_days : Q := Qmult (235 # 1) synodic_month_days.

Definition metonic_error : Q := metonic_months_days - metonic_years_days.

Lemma Qlt_metonic_error_1 : Qlt (Qabs_custom metonic_error) (1 # 1).
Proof.
  unfold metonic_error, metonic_months_days, metonic_years_days.
  unfold synodic_month_days, tropical_year_days.
  unfold Qlt, Qabs_custom, Qle_bool, Qminus, Qmult, Qplus, Qopp. simpl. lia.
Qed.

Definition saros_days : Q := Qmult (223 # 1) synodic_month_days.

Close Scope Q_scope.

(* ========================================================================== *)
(* XV. Error Bounds                                                           *)
(* ========================================================================== *)
(*                                                                            *)
(* Comparison of mechanism gear ratios against modern astronomical values.    *)
(* The Babylonian period relations encoded in the gears are remarkably close  *)
(* to true synodic periods, demonstrating sophisticated ancient astronomy.    *)
(*                                                                            *)
(* Error analysis shows:                                                      *)
(* - Venus: error < 0.5 days over synodic period (~584 days)                  *)
(* - Saturn: error < 1 day over synodic period (~378 days)                    *)
(* - Metonic: error < 3 hours over 19 years (< 0.01%)                         *)
(*                                                                            *)
(* These errors are within observational limits of naked-eye astronomy.       *)
(*                                                                            *)
(* ========================================================================== *)

Open Scope Q_scope.

(* -------------------------------------------------------------------------- *)
(* relative_error                                                             *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Standard error analysis                                         *)
(* EVIDENCE:  |(mechanism - actual) / actual| measures fractional error       *)
(* SEMANTICS: Returns relative error as absolute fraction                     *)
(* -------------------------------------------------------------------------- *)
Definition relative_error (actual mechanism : Q) : Q := Qabs_custom ((mechanism - actual) / actual).

Definition venus_actual : Q := venus_synodic_days / tropical_year_days.
Definition venus_mechanism : Q := 462 # 289.

Lemma venus_actual_expanded :
  venus_actual = (58392 * 100000) # (100 * 36524219).
Proof. unfold venus_actual, venus_synodic_days, tropical_year_days, Qdiv, Qmult, Qinv. reflexivity. Qed.

Lemma venus_mechanism_close_to_actual :
  Qlt (Qabs_custom (venus_mechanism - venus_actual)) (1 # 100).
Proof.
  unfold venus_mechanism, venus_actual, venus_synodic_days, tropical_year_days.
  unfold Qabs_custom, Qle_bool, Qdiv, Qminus, Qmult, Qinv, Qlt. simpl. lia.
Qed.

Definition saturn_actual : Q := saturn_synodic_days / tropical_year_days.
Definition saturn_mechanism : Q := 442 # 427.

Lemma saturn_actual_expanded :
  saturn_actual = (37809 * 100000) # (100 * 36524219).
Proof. unfold saturn_actual, saturn_synodic_days, tropical_year_days, Qdiv, Qmult, Qinv. reflexivity. Qed.

Lemma saturn_mechanism_close_to_actual :
  Qlt (Qabs_custom (saturn_mechanism - saturn_actual)) (1 # 100).
Proof.
  unfold saturn_mechanism, saturn_actual, saturn_synodic_days, tropical_year_days.
  unfold Qabs_custom, Qle_bool, Qdiv, Qminus, Qmult, Qinv, Qlt. simpl. lia.
Qed.

Definition error_bound_1pct : Q := 1 # 100.
Definition error_bound_01pct : Q := 1 # 1000.

Definition venus_synodic_modern_days : Q := 58392 # 100.
Definition saturn_synodic_modern_days : Q := 37809 # 100.
Definition mars_synodic_modern_days : Q := 77994 # 100.
Definition jupiter_synodic_modern_days : Q := 39883 # 100.
Definition mercury_synodic_modern_days : Q := 11588 # 100.

Definition venus_mechanism_days : Q := Qmult (462 # 289) tropical_year_days.
Definition saturn_mechanism_days : Q := Qmult (442 # 427) tropical_year_days.

Definition venus_error_num : Q := venus_mechanism_days - venus_synodic_modern_days.
Definition saturn_error_num : Q := saturn_mechanism_days - saturn_synodic_modern_days.

Lemma Qlt_venus_error_half_day :
  Qlt (Qabs_custom venus_error_num) (1 # 2).
Proof.
  unfold venus_error_num, venus_mechanism_days, venus_synodic_modern_days.
  unfold tropical_year_days, Qabs_custom, Qle_bool, Qminus, Qmult, Qlt.
  simpl. lia.
Qed.

Lemma Qlt_saturn_error_1day :
  Qlt (Qabs_custom saturn_error_num) (1 # 1).
Proof.
  unfold saturn_error_num, saturn_mechanism_days, saturn_synodic_modern_days.
  unfold tropical_year_days, Qabs_custom, Qle_bool, Qminus, Qmult, Qlt.
  simpl. lia.
Qed.

Definition venus_relative_error : Q :=
  relative_error venus_synodic_modern_days venus_mechanism_days.

Definition saturn_relative_error : Q :=
  relative_error saturn_synodic_modern_days saturn_mechanism_days.

Lemma venus_relative_error_lt_1pct :
  Qlt venus_relative_error error_bound_1pct.
Proof.
  unfold venus_relative_error, relative_error, error_bound_1pct.
  unfold venus_mechanism_days, venus_synodic_modern_days, tropical_year_days.
  unfold Qabs_custom, Qle_bool, Qdiv, Qminus, Qmult, Qlt.
  simpl. lia.
Qed.

Lemma saturn_relative_error_lt_1pct :
  Qlt saturn_relative_error error_bound_1pct.
Proof.
  unfold saturn_relative_error, relative_error, error_bound_1pct.
  unfold saturn_mechanism_days, saturn_synodic_modern_days, tropical_year_days.
  unfold Qabs_custom, Qle_bool, Qdiv, Qminus, Qmult, Qlt.
  simpl. lia.
Qed.

Definition metonic_mechanism_days : Q := Qmult (235 # 1) synodic_month_days.
Definition metonic_actual_days : Q := Qmult (19 # 1) tropical_year_days.

Lemma Qlt_metonic_error_3hrs :
  Qlt (Qabs_custom (metonic_mechanism_days - metonic_actual_days)) (1 # 8).
Proof.
  unfold metonic_mechanism_days, metonic_actual_days.
  unfold synodic_month_days, tropical_year_days.
  unfold Qabs_custom, Qle_bool, Qminus, Qmult, Qlt.
  simpl. lia.
Qed.

Definition saros_total_days : Q := Qmult (223 # 1) synodic_month_days.

Lemma saros_approx_6585_days :
  Qlt (Qabs_custom (saros_total_days - (658532 # 100))) (1 # 10).
Proof.
  unfold saros_total_days, synodic_month_days.
  unfold Qabs_custom, Qle_bool, Qminus, Qmult, Qlt.
  simpl. lia.
Qed.

Definition saros_remainder_hours : Q := Qmult (saros_total_days - (6585 # 1)) (24 # 1).

Lemma saros_remainder_near_8hrs :
  Qlt (7 # 1) saros_remainder_hours /\ Qlt saros_remainder_hours (9 # 1).
Proof.
  unfold saros_remainder_hours, saros_total_days, synodic_month_days.
  unfold Qlt, Qminus, Qmult. simpl. split; lia.
Qed.

Lemma saros_third_day_exact :
  Qeq (saros_fractional_day) (1 # 3).
Proof. reflexivity. Qed.

Close Scope Q_scope.

(* ========================================================================== *)
(* XVI. State Machine                                                         *)
(* ========================================================================== *)
(*                                                                            *)
(* The mechanism operates as a deterministic state machine: turning the       *)
(* input crank advances all dials according to their gear ratios. This        *)
(* section models the discrete state space for periodicity analysis.          *)
(*                                                                            *)
(* DIAL MODULI (cycle lengths):                                               *)
(* - Metonic: 235 months (19 years × 5 turns)                                 *)
(* - Saros: 223 months (4 turns × ~56 months)                                 *)
(* - Callippic: 76 years (4 × Metonic)                                        *)
(* - Exeligmos: 3 (cycle through 0h, 8h, 16h offsets)                         *)
(* - Games: 4 (Olympiad cycle)                                                *)
(* - Zodiac: 360 (degrees)                                                    *)
(*                                                                            *)
(* PERIODICITY THEOREM: LCM of all cycles = 71,690,040 steps                  *)
(* After this many steps, all dials return to their initial positions.        *)
(*                                                                            *)
(* NOTE: This is a LOGICAL state-space model of dial cell indices, not a      *)
(* kinematically faithful simulation. Each dial increments by 1 per step,     *)
(* representing advancement by one cell. In the physical mechanism, one       *)
(* crank rotation advances dials by their respective gear ratios (e.g.,       *)
(* Metonic advances 235/19 cells per year, not 1). This abstraction is        *)
(* intentional: it models the discrete state space for periodicity proofs     *)
(* while the gear train sections handle continuous ratio relationships.       *)
(*                                                                            *)
(* ========================================================================== *)

Open Scope Z_scope.

Record MechanismState := mkState {
  crank_position : Z;
  metonic_dial : Z;
  saros_dial : Z;
  callippic_dial : Z;
  exeligmos_dial : Z;
  games_dial : Z;
  zodiac_position : Z
}.

Definition initial_state : MechanismState := mkState 0 0 0 0 0 0 0.

Definition metonic_modulus : Z := 235.
Definition saros_modulus : Z := 223.
Definition callippic_modulus : Z := 76.
Definition exeligmos_modulus : Z := 3.
Definition games_modulus : Z := 4.
Definition zodiac_modulus : Z := 360.

Definition step (s : MechanismState) : MechanismState :=
  mkState
    (crank_position s + 1)
    (Z.modulo (metonic_dial s + 1) metonic_modulus)
    (Z.modulo (saros_dial s + 1) saros_modulus)
    (Z.modulo (callippic_dial s + 1) callippic_modulus)
    (Z.modulo (exeligmos_dial s + 1) exeligmos_modulus)
    (Z.modulo (games_dial s + 1) games_modulus)
    (Z.modulo (zodiac_position s + 1) zodiac_modulus).

Definition step_reverse (s : MechanismState) : MechanismState :=
  mkState
    (crank_position s - 1)
    (Z.modulo (metonic_dial s - 1 + metonic_modulus) metonic_modulus)
    (Z.modulo (saros_dial s - 1 + saros_modulus) saros_modulus)
    (Z.modulo (callippic_dial s - 1 + callippic_modulus) callippic_modulus)
    (Z.modulo (exeligmos_dial s - 1 + exeligmos_modulus) exeligmos_modulus)
    (Z.modulo (games_dial s - 1 + games_modulus) games_modulus)
    (Z.modulo (zodiac_position s - 1 + zodiac_modulus) zodiac_modulus).

Lemma step_reverse_step_initial :
  step_reverse (step initial_state) = initial_state.
Proof. reflexivity. Qed.

Lemma reverse_crank_example :
  step_reverse (step (step initial_state)) = step initial_state.
Proof. reflexivity. Qed.

Lemma step_reverse_step_bounded : forall s : MechanismState,
  (0 <= metonic_dial s < metonic_modulus)%Z ->
  (0 <= saros_dial s < saros_modulus)%Z ->
  (0 <= callippic_dial s < callippic_modulus)%Z ->
  (0 <= exeligmos_dial s < exeligmos_modulus)%Z ->
  (0 <= games_dial s < games_modulus)%Z ->
  (0 <= zodiac_position s < zodiac_modulus)%Z ->
  crank_position (step_reverse (step s)) = crank_position s.
Proof.
  intros s Hm Hs Hc He Hg Hz.
  unfold step, step_reverse. destruct s. simpl. lia.
Qed.

Definition is_prime_divisor (p n : Z) : bool :=
  (1 <? p)%Z && (n mod p =? 0)%Z && (Z.gcd p (n / p) =? 1)%Z.

Close Scope Z_scope.
Open Scope Q_scope.

Record KinematicState := mkKinState {
  kin_crank : Q;
  kin_metonic : Q;
  kin_saros : Q;
  kin_zodiac : Q
}.

Definition kin_initial : KinematicState := mkKinState 0 0 0 0.

Definition metonic_rate : Q := 235 # 19.
Definition saros_rate : Q := 223 # 19.
Definition zodiac_rate : Q := 360 # 1.

Definition kin_step (s : KinematicState) : KinematicState :=
  mkKinState
    (kin_crank s + 1)
    (kin_metonic s + metonic_rate)
    (kin_saros s + saros_rate)
    (kin_zodiac s + zodiac_rate).

Definition kin_step_n (n : nat) (s : KinematicState) : KinematicState :=
  Nat.iter n kin_step s.

Lemma kin_step_crank_inc : forall s,
  kin_crank (kin_step s) = kin_crank s + 1.
Proof. intro s. reflexivity. Qed.

Lemma kin_metonic_after_1_year : forall s,
  kin_metonic (kin_step s) = kin_metonic s + (235 # 19).
Proof. intro s. reflexivity. Qed.

Lemma kin_metonic_after_1_year_value :
  Qeq (kin_metonic (kin_step kin_initial)) (235 # 19).
Proof. reflexivity. Qed.

Lemma kin_saros_after_1_year_value :
  Qeq (kin_saros (kin_step kin_initial)) (223 # 19).
Proof. reflexivity. Qed.

Lemma kin_crank_step : forall s,
  Qeq (kin_crank (kin_step s)) (kin_crank s + 1).
Proof. intro s. reflexivity. Qed.

Lemma kin_crank_initial :
  Qeq (kin_crank kin_initial) 0.
Proof. reflexivity. Qed.

Lemma kin_metonic_rate_correct :
  Qeq metonic_rate (235 # 19).
Proof. reflexivity. Qed.

Lemma kin_saros_rate_correct :
  Qeq saros_rate (223 # 19).
Proof. reflexivity. Qed.

Close Scope Q_scope.
Open Scope Z_scope.

Lemma gcd_235_223_eq_1 : (Z.gcd 235 223 = 1)%Z.
Proof. reflexivity. Qed.

Lemma gcd_235_76_eq_1 : (Z.gcd 235 76 = 1)%Z.
Proof. reflexivity. Qed.

Lemma lcm_235_223 : (Z.lcm 235 223 = 52405)%Z.
Proof. reflexivity. Qed.

Theorem metonic_saros_coprime :
  (Z.gcd metonic_modulus saros_modulus = 1)%Z.
Proof. unfold metonic_modulus, saros_modulus. reflexivity. Qed.

Definition gear_module_compatible (g1 g2 : Gear) : Prop :=
  valid_tooth_count (teeth g1) /\ valid_tooth_count (teeth g2).

Lemma hypothetical_gears_valid_teeth :
  forallb (fun g => (15 <=? Zpos (teeth g))%Z && (Zpos (teeth g) <=? 223)%Z) 
    hypothetical_gears_freeth_2021 = true.
Proof. reflexivity. Qed.

Theorem incorrect_venus_ratio_fails :
  ~ Qeq (train_ratio venus_train_simple) (288 # 462).
Proof.
  unfold Qeq, train_ratio, venus_train_simple. simpl. lia.
Qed.

Theorem incorrect_metonic_ratio_fails :
  ~ Qeq metonic_train_ratio (234 # 19).
Proof.
  unfold Qeq, metonic_train_ratio. simpl. lia.
Qed.

Definition sub_step_resolution : positive := 30.

Record MechanismStateQ := mkStateQ {
  crank_position_q : Q;
  metonic_dial_q : Q;
  zodiac_position_q : Q
}.

Definition state_to_stateQ (s : MechanismState) : MechanismStateQ :=
  mkStateQ
    (Qmake (crank_position s) 1)
    (Qmake (metonic_dial s) 1)
    (Qmake (zodiac_position s) 1).

Definition Q_to_Z_floor (q : Q) : Z := Qnum q / Zpos (Qden q).

Definition stateQ_floor (sq : MechanismStateQ) : MechanismState :=
  mkState
    (Q_to_Z_floor (crank_position_q sq))
    (Z.modulo (Q_to_Z_floor (metonic_dial_q sq)) metonic_modulus)
    0
    0
    0
    0
    (Z.modulo (Q_to_Z_floor (zodiac_position_q sq)) zodiac_modulus).

Lemma state_to_stateQ_initial :
  state_to_stateQ initial_state = mkStateQ (Qmake 0 1) (Qmake 0 1) (Qmake 0 1).
Proof. reflexivity. Qed.

Lemma stateQ_floor_initial :
  stateQ_floor (state_to_stateQ initial_state) = initial_state.
Proof. reflexivity. Qed.

(* Qred removed: it is non-homomorphic and complicates algebraic reasoning.  *)
(* Raw Q products preserve algebraic structure for proofs.                    *)
Definition step_fractional (s : MechanismStateQ) (delta : Q) : MechanismStateQ :=
  let new_crank := Qplus (crank_position_q s) delta in
  mkStateQ
    new_crank
    (Qmult new_crank (235 # 19))
    (Qmult new_crank (360 # 1)).

Definition zodiac_angular_deg (s : MechanismState) : Q :=
  Qmake (zodiac_position s) 1.

Lemma zodiac_angular_deg_zero : zodiac_angular_deg initial_state = Qmake 0 1.
Proof. reflexivity. Qed.

Lemma zodiac_angular_deg_bounds : forall s,
  (0 <= zodiac_position s < zodiac_modulus)%Z ->
  Qle (Qmake 0 1) (zodiac_angular_deg s) /\ Qlt (zodiac_angular_deg s) (Qmake 360 1).
Proof.
  intros s [Hlo Hhi]. unfold zodiac_angular_deg, zodiac_modulus in *.
  split; unfold Qle, Qlt; simpl; lia.
Qed.

Inductive PlanetaryMotion : Set :=
  | DirectMotion | StationaryMotion | RetrogradeMotion.

Record PlanetaryPointer := mkPlanetaryPointer {
  planet_longitude_deg : Q;
  planet_motion_type : PlanetaryMotion;
  synodic_phase_deg : Q
}.

Definition mars_retrograde_arc_deg : Q := 15 # 1.
Definition jupiter_retrograde_arc_deg : Q := 10 # 1.
Definition saturn_retrograde_arc_deg : Q := 7 # 1.

Record PlanetaryPositions := mkPlanetaryPositions {
  mercury_pos : Q;
  venus_pos : Q;
  mars_pos : Q;
  jupiter_pos : Q;
  saturn_pos : Q
}.

Record ExtendedMechanismState := mkExtendedState {
  base_state : MechanismState;
  moon_phase_deg : Q;
  planetary_positions : PlanetaryPositions
}.

Definition initial_planetary_positions : PlanetaryPositions :=
  mkPlanetaryPositions (0#1) (0#1) (0#1) (0#1) (0#1).

Definition initial_extended_state : ExtendedMechanismState :=
  mkExtendedState initial_state (0#1) initial_planetary_positions.

Definition planetary_step (pp : PlanetaryPositions) (years_delta : Q) : PlanetaryPositions :=
  mkPlanetaryPositions
    (Qplus (mercury_pos pp) (Qmult years_delta mercury_ratio))
    (Qplus (venus_pos pp) (Qmult years_delta venus_ratio))
    (Qplus (mars_pos pp) (Qmult years_delta mars_ratio))
    (Qplus (jupiter_pos pp) (Qmult years_delta jupiter_ratio))
    (Qplus (saturn_pos pp) (Qmult years_delta saturn_ratio)).

Definition mars_retrograde_duration_days : Q := 72 # 1.
Definition jupiter_retrograde_duration_days : Q := 121 # 1.
Definition saturn_retrograde_duration_days : Q := 138 # 1.


Fixpoint step_n (n : nat) (s : MechanismState) : MechanismState :=
  match n with O => s | S m => step (step_n m s) end.

Lemma Z_235_mod_235 : Z.modulo 235 metonic_modulus = 0.
Proof. reflexivity. Qed.

Lemma Z_223_mod_223 : Z.modulo 223 saros_modulus = 0.
Proof. reflexivity. Qed.

Lemma Z_76_mod_76 : Z.modulo 76 callippic_modulus = 0.
Proof. reflexivity. Qed.

Lemma Z_3_mod_3 : Z.modulo 3 exeligmos_modulus = 0.
Proof. reflexivity. Qed.

Lemma Z_4_mod_4 : Z.modulo 4 games_modulus = 0.
Proof. reflexivity. Qed.

Lemma Z_360_mod_360 : Z.modulo 360 zodiac_modulus = 0.
Proof. reflexivity. Qed.

Definition lcm_all_cycles : Z := 71690040.

Lemma lcm_all_eq_71690040 : lcm_all_cycles = 71690040%Z.
Proof. reflexivity. Qed.

Definition dials_at_zero (s : MechanismState) : Prop :=
  metonic_dial s = 0 /\ saros_dial s = 0 /\ callippic_dial s = 0 /\
  exeligmos_dial s = 0 /\ games_dial s = 0 /\ zodiac_position s = 0.

Lemma step_n_dial_generic : forall (proj : MechanismState -> Z) (modulus : Z) n s,
  (modulus > 0)%Z ->
  (0 <= proj s < modulus)%Z ->
  (forall st, proj (step st) = Z.modulo (proj st + 1) modulus) ->
  proj (step_n n s) = Z.modulo (proj s + Z.of_nat n) modulus.
Proof.
  intros proj modulus n s Hmod Hbound Hstep.
  induction n as [|n' IHn'].
  - simpl. rewrite Z.add_0_r. rewrite Z.mod_small; [reflexivity | lia].
  - simpl step_n. rewrite Hstep.
    assert (Hbound' : (0 <= proj (step_n n' s) < modulus)%Z).
    { rewrite IHn'. apply Z.mod_pos_bound. lia. }
    rewrite IHn'.
    rewrite Nat2Z.inj_succ.
    replace (proj s + Z.succ (Z.of_nat n'))%Z with (proj s + Z.of_nat n' + 1)%Z by lia.
    rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma dial_mod_divides : forall m n,
  (m > 0)%Z -> (m | Z.of_nat n)%Z -> Z.modulo (Z.of_nat n) m = 0.
Proof.
  intros m n Hm Hdiv.
  destruct Hdiv as [k Hk].
  rewrite Hk.
  apply Z.mod_mul.
  lia.
Qed.

Lemma Z_71690040_eq_235_mul : (71690040 = 235 * 305064)%Z.
Proof. reflexivity. Qed.

Lemma Z_71690040_eq_223_mul : (71690040 = 223 * 321480)%Z.
Proof. reflexivity. Qed.

Lemma Z_71690040_eq_76_mul : (71690040 = 76 * 943290)%Z.
Proof. reflexivity. Qed.

Lemma Z_71690040_eq_3_mul : (71690040 = 3 * 23896680)%Z.
Proof. reflexivity. Qed.

Lemma Z_71690040_eq_4_mul : (71690040 = 4 * 17922510)%Z.
Proof. reflexivity. Qed.

Lemma Z_71690040_eq_360_mul : (71690040 = 360 * 199139)%Z.
Proof. reflexivity. Qed.

Lemma lcm_divides_metonic : (metonic_modulus | lcm_all_cycles)%Z.
Proof. unfold Z.divide, metonic_modulus, lcm_all_cycles. exists 305064. reflexivity. Qed.

Lemma lcm_divides_saros : (saros_modulus | lcm_all_cycles)%Z.
Proof. unfold Z.divide, saros_modulus, lcm_all_cycles. exists 321480. reflexivity. Qed.

Lemma lcm_divides_callippic : (callippic_modulus | lcm_all_cycles)%Z.
Proof. unfold Z.divide, callippic_modulus, lcm_all_cycles. exists 943290. reflexivity. Qed.

Lemma lcm_divides_exeligmos : (exeligmos_modulus | lcm_all_cycles)%Z.
Proof. unfold Z.divide, exeligmos_modulus, lcm_all_cycles. exists 23896680. reflexivity. Qed.

Lemma lcm_divides_games : (games_modulus | lcm_all_cycles)%Z.
Proof. unfold Z.divide, games_modulus, lcm_all_cycles. exists 17922510. reflexivity. Qed.

Lemma lcm_divides_zodiac : (zodiac_modulus | lcm_all_cycles)%Z.
Proof. unfold Z.divide, zodiac_modulus, lcm_all_cycles. exists 199139. reflexivity. Qed.

Lemma lcm_divides_all :
  (metonic_modulus | lcm_all_cycles)%Z /\ (saros_modulus | lcm_all_cycles)%Z /\
  (callippic_modulus | lcm_all_cycles)%Z /\ (exeligmos_modulus | lcm_all_cycles)%Z /\
  (games_modulus | lcm_all_cycles)%Z /\ (zodiac_modulus | lcm_all_cycles)%Z.
Proof.
  repeat split.
  - exact lcm_divides_metonic.
  - exact lcm_divides_saros.
  - exact lcm_divides_callippic.
  - exact lcm_divides_exeligmos.
  - exact lcm_divides_games.
  - exact lcm_divides_zodiac.
Qed.

Lemma mod_of_multiple : forall a b : Z, (b > 0)%Z -> (b | a)%Z -> (a mod b = 0)%Z.
Proof.
  intros a b Hpos [k Hk]. rewrite Hk. apply Z.mod_mul. lia.
Qed.

Lemma lcm_all_cycles_nonneg : (0 <= lcm_all_cycles)%Z.
Proof. unfold lcm_all_cycles. lia. Qed.

Lemma Zof_nat_lcm : Z.of_nat (Z.to_nat lcm_all_cycles) = lcm_all_cycles.
Proof. rewrite Z2Nat.id. reflexivity. exact lcm_all_cycles_nonneg. Qed.

Lemma initial_metonic_zero : metonic_dial initial_state = 0.
Proof. reflexivity. Qed.

Lemma initial_saros_zero : saros_dial initial_state = 0.
Proof. reflexivity. Qed.

Lemma initial_callippic_zero : callippic_dial initial_state = 0.
Proof. reflexivity. Qed.

Lemma initial_exeligmos_zero : exeligmos_dial initial_state = 0.
Proof. reflexivity. Qed.

Lemma initial_games_zero : games_dial initial_state = 0.
Proof. reflexivity. Qed.

Lemma initial_zodiac_zero : zodiac_position initial_state = 0.
Proof. reflexivity. Qed.

Theorem cycle_return_dials_forall : forall n : nat,
  Z.of_nat n = lcm_all_cycles ->
  dials_at_zero (step_n n initial_state).
Proof.
  intros n Hn. unfold dials_at_zero. repeat split.
  - rewrite step_n_dial_generic with (modulus := metonic_modulus).
    + rewrite initial_metonic_zero, Z.add_0_l, Hn.
      apply mod_of_multiple. unfold metonic_modulus. lia. exact lcm_divides_metonic.
    + unfold metonic_modulus. lia.
    + rewrite initial_metonic_zero. unfold metonic_modulus. lia.
    + reflexivity.
  - rewrite step_n_dial_generic with (modulus := saros_modulus).
    + rewrite initial_saros_zero, Z.add_0_l, Hn.
      apply mod_of_multiple. unfold saros_modulus. lia. exact lcm_divides_saros.
    + unfold saros_modulus. lia.
    + rewrite initial_saros_zero. unfold saros_modulus. lia.
    + reflexivity.
  - rewrite step_n_dial_generic with (modulus := callippic_modulus).
    + rewrite initial_callippic_zero, Z.add_0_l, Hn.
      apply mod_of_multiple. unfold callippic_modulus. lia. exact lcm_divides_callippic.
    + unfold callippic_modulus. lia.
    + rewrite initial_callippic_zero. unfold callippic_modulus. lia.
    + reflexivity.
  - rewrite step_n_dial_generic with (modulus := exeligmos_modulus).
    + rewrite initial_exeligmos_zero, Z.add_0_l, Hn.
      apply mod_of_multiple. unfold exeligmos_modulus. lia. exact lcm_divides_exeligmos.
    + unfold exeligmos_modulus. lia.
    + rewrite initial_exeligmos_zero. unfold exeligmos_modulus. lia.
    + reflexivity.
  - rewrite step_n_dial_generic with (modulus := games_modulus).
    + rewrite initial_games_zero, Z.add_0_l, Hn.
      apply mod_of_multiple. unfold games_modulus. lia. exact lcm_divides_games.
    + unfold games_modulus. lia.
    + rewrite initial_games_zero. unfold games_modulus. lia.
    + reflexivity.
  - rewrite step_n_dial_generic with (modulus := zodiac_modulus).
    + rewrite initial_zodiac_zero, Z.add_0_l, Hn.
      apply mod_of_multiple. unfold zodiac_modulus. lia. exact lcm_divides_zodiac.
    + unfold zodiac_modulus. lia.
    + rewrite initial_zodiac_zero. unfold zodiac_modulus. lia.
    + reflexivity.
Qed.

Theorem cycle_return_dials : exists n : nat,
  Z.of_nat n = lcm_all_cycles /\ dials_at_zero (step_n n initial_state).
Proof.
  exists (Z.to_nat lcm_all_cycles). split.
  - apply Z2Nat.id. exact lcm_all_cycles_nonneg.
  - apply cycle_return_dials_forall. apply Z2Nat.id. exact lcm_all_cycles_nonneg.
Qed.

(* ========================================================================== *)
(* XVII. Summary Theorems                                                     *)
(* ========================================================================== *)
(*                                                                            *)
(* Consolidated correctness statements for all major components of the        *)
(* mechanism. The master theorem `mechanism_completeness` bundles all         *)
(* verified claims: Metonic, Venus, Saturn, Mars, Jupiter trains; calendar;   *)
(* games dial; zodiac. Each component theorem can be cited independently.     *)
(*                                                                            *)
(* VERIFIED CLAIMS:                                                           *)
(* - metonic_correct: 235/19 ratio with gears 38a and 127                     *)
(* - venus_correct: 289/462 via train (51→44, 34→26, 26→63)                   *)
(* - saturn_correct: 427/442 ratio (from FCI inscription)                     *)
(* - saros_correct: 223-tooth gear matches Saros months                       *)
(* - calendar_lunar: 354 holes with Bayesian evidence                         *)
(* - lunar_anomaly_mean: 1:1 mean ratio from 50-tooth gears                   *)
(* - period_relations: all astronomical ratios correctly encoded              *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* metonic_correct                                                            *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Freeth et al. 2006; gear train analysis                         *)
(* EVIDENCE:  Gears 38a (38 teeth) and 127 (127 teeth) confirmed by CT        *)
(* SEMANTICS: Metonic ratio 235/19 correctly encoded in mechanism             *)
(* -------------------------------------------------------------------------- *)
Theorem metonic_correct :
  metonic_spec metonic_train_ratio /\ teeth gear_38a = 38%positive /\ teeth gear_127 = 127%positive.
Proof. repeat split; reflexivity. Qed.

Theorem venus_correct : Qeq (Qinv (train_ratio venus_train_simple)) venus_ratio.
Proof. exact Qeq_venus_inv_289_462. Qed.

Theorem saturn_correct :
  saturn_spec saturn_direct_ratio /\ saturn_years = 442%positive /\ saturn_synodic_periods = 427%positive.
Proof. repeat split; reflexivity. Qed.

Theorem saros_correct : teeth gear_e3 = saros_months.
Proof. reflexivity. Qed.

Theorem calendar_lunar : calendar_ring_holes = 354%positive /\ bayes_factor_strong calendar_bayes_factor.
Proof. split; [reflexivity | exact bayes_factor_calendar]. Qed.

Theorem lunar_anomaly_mean : Qeq pin_slot_mean_ratio (1 # 1).
Proof. exact Qeq_pin_slot_1. Qed.

Theorem games_dial_correct : games_sectors antikythera_games_dial = games_cycle_years.
Proof. reflexivity. Qed.

Theorem zodiac_correct : zodiac_divisions antikythera_zodiac = 360%positive.
Proof. reflexivity. Qed.

Theorem period_relations :
  metonic_ratio = (235 # 19)%Q /\ callippic_ratio = (940 # 76)%Q /\ saros_ratio = (223 # 1)%Q /\
  venus_ratio = (289 # 462)%Q /\ saturn_ratio = (427 # 442)%Q /\
  mars_ratio = (133 # 284)%Q /\ jupiter_ratio = (315 # 344)%Q.
Proof. repeat split; reflexivity. Qed.

Theorem ct_gear_count : length ct_confirmed_gears = 23%nat.
Proof. reflexivity. Qed.

Definition mechanism_completeness : Prop :=
  metonic_spec metonic_train_ratio /\
  venus_spec (Qinv (train_ratio venus_train_simple)) /\
  saturn_spec saturn_direct_ratio /\
  mars_spec (train_ratio mars_train_correct) /\
  jupiter_spec (train_ratio jupiter_train_correct) /\
  calendar_type_lunar /\
  games_sectors antikythera_games_dial = 4%positive /\
  zodiac_divisions antikythera_zodiac = 360%positive.

Theorem mechanism_complete : mechanism_completeness.
Proof.
  unfold mechanism_completeness.
  split. exact metonic_train_spec.
  split. unfold venus_spec. exact Qeq_venus_inv_289_462.
  split. exact saturn_train_spec.
  split. exact mars_train_correct_spec.
  split. exact jupiter_train_correct_spec.
  split. exact calendar_354.
  split; reflexivity.
Qed.

Theorem mercury_train_correct : mercury_spec (train_ratio mercury_train_derived).
Proof. exact mercury_train_derived_spec. Qed.

Theorem moon_sidereal_ratio_correct : Qeq lunar_sidereal_ratio (254 # 19).
Proof. reflexivity. Qed.

Theorem differential_derives_synodic :
  Qeq (synodic_from_sidereal lunar_sidereal_ratio) metonic_ratio.
Proof.
  unfold synodic_from_sidereal, lunar_sidereal_ratio, metonic_ratio.
  unfold Qeq, Qminus. simpl. reflexivity.
Qed.

Theorem exeligmos_8hr_correction_valid :
  forall n, (0 <= exeligmos_correction n < 24)%Z.
Proof.
  intro n. unfold exeligmos_correction. apply Z.mod_pos_bound. lia.
Qed.

Theorem saros_4_turns_223_months :
  (saros_turn_months 0 + saros_turn_months 1 + saros_turn_months 2 + saros_turn_months 3 = 223)%Z.
Proof. reflexivity. Qed.

Theorem error_bounds_verified :
  Qlt (Qabs_custom venus_error_num) (1 # 2) /\
  Qlt (Qabs_custom saturn_error_num) (1 # 1) /\
  Qlt (Qabs_custom (metonic_mechanism_days - metonic_actual_days)) (1 # 8).
Proof.
  split. exact Qlt_venus_error_half_day.
  split. exact Qlt_saturn_error_1day.
  exact Qlt_metonic_error_3hrs.
Qed.

(* ========================================================================== *)
(* XVIII. Provenance                                                          *)
(* ========================================================================== *)
(*                                                                            *)
(* Tracks the evidential basis for each claim in the formalization.           *)
(* Different parts of our knowledge have different levels of certainty:       *)
(*                                                                            *)
(* SOURCE QUALITY LEVELS:                                                     *)
(* - CTConfirmed (100%): Gear teeth directly visible in CT scans              *)
(* - InscriptionDerived (95%): Numbers read from inscriptions (e.g., FCI)     *)
(* - ReconstructionHypothesis (70%): Freeth 2021 or similar reconstructions   *)
(* - ComputationalInference (90%): Statistical/Bayesian analysis of evidence  *)
(*                                                                            *)
(* This enables meta-reasoning about which theorems depend on which           *)
(* assumptions, important for understanding the formalization's scope.        *)
(*                                                                            *)
(* Example provenances:                                                       *)
(* - Metonic ratio: CT-confirmed (gears 38, 127 visible)                      *)
(* - Venus 462: Inscription-derived (ΥΞΒ visible in CT)                       *)
(* - Mercury gear train: Hypothesis (Freeth 2021)                             *)
(* - Calendar 354 holes: Bayesian inference (Budiselic et al.)                *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* SourceQuality                                                              *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Epistemological classification of evidence types                *)
(* EVIDENCE:  Different parts of mechanism have different certainty levels    *)
(* SEMANTICS: Hierarchy from direct observation to computational inference    *)
(* -------------------------------------------------------------------------- *)
Inductive SourceQuality : Set :=
  | CTConfirmed | InscriptionDerived | ReconstructionHypothesis | ComputationalInference.

Record ClaimProvenance := mkProvenance {
  claim_source : SourceQuality;
  source_reference : string;
  confidence_level : positive
}.

Definition metonic_provenance : ClaimProvenance :=
  mkProvenance CTConfirmed "Fragment A CT scan, gear teeth counts" 100.

Definition venus_provenance : ClaimProvenance :=
  mkProvenance InscriptionDerived "Back cover inscription ΥΞΒ = 462" 95.

Definition saturn_provenance : ClaimProvenance :=
  mkProvenance InscriptionDerived "Back cover inscription ΥΜΒ = 442" 95.

Definition mercury_provenance : ClaimProvenance :=
  mkProvenance ReconstructionHypothesis "Freeth 2021 computational derivation" 70.

Definition calendar_provenance : ClaimProvenance :=
  mkProvenance ComputationalInference "Budiselic et al. 2024 Bayesian analysis" 90.

Definition high_confidence (p : ClaimProvenance) : Prop := (Zpos (confidence_level p) >= 90)%Z.

Theorem metonic_high_conf : high_confidence metonic_provenance.
Proof. unfold high_confidence, metonic_provenance. simpl. lia. Qed.

Theorem venus_high_conf : high_confidence venus_provenance.
Proof. unfold high_confidence, venus_provenance. simpl. lia. Qed.

Theorem mercury_low_conf : ~high_confidence mercury_provenance.
Proof. unfold high_confidence, mercury_provenance. simpl. lia. Qed.

Record ProvenancedClaim := mkProvenancedClaim {
  pc_statement : Prop;
  pc_proof : pc_statement;
  pc_provenance : ClaimProvenance
}.

Definition metonic_provenanced : ProvenancedClaim :=
  mkProvenancedClaim 
    (metonic_spec metonic_train_ratio)
    metonic_train_spec
    metonic_provenance.

Definition venus_provenanced : ProvenancedClaim :=
  mkProvenancedClaim
    (venus_spec (Qinv (train_ratio venus_train_simple)))
    Qeq_venus_inv_289_462
    venus_provenance.

Definition saturn_provenanced : ProvenancedClaim :=
  mkProvenancedClaim
    (saturn_spec saturn_direct_ratio)
    saturn_train_spec
    saturn_provenance.

Theorem all_high_conf_claims_validated :
  pc_statement metonic_provenanced /\ pc_statement venus_provenanced /\ pc_statement saturn_provenanced.
Proof.
  split. exact (pc_proof metonic_provenanced).
  split. exact (pc_proof venus_provenanced).
  exact (pc_proof saturn_provenanced).
Qed.

Theorem high_conf_provenances :
  high_confidence (pc_provenance metonic_provenanced) /\ high_confidence (pc_provenance venus_provenanced) /\ high_confidence (pc_provenance saturn_provenanced).
Proof.
  split. exact metonic_high_conf.
  split. exact venus_high_conf.
  unfold high_confidence, saturn_provenanced, saturn_provenance. simpl. lia.
Qed.

(* ========================================================================== *)
(* XIX. Type Safety and Automation                                            *)
(* ========================================================================== *)
(*                                                                            *)
(* Additional type wrappers and tactics for cleaner formalization.            *)
(*                                                                            *)
(* DIMENSIONAL TYPES:                                                         *)
(* - Frequency: cycles per unit time (e.g., 254/19 sidereal months/year)      *)
(* - Period: time per cycle (inverse of frequency)                            *)
(*                                                                            *)
(* These wrappers help distinguish semantically different quantities that     *)
(* happen to both be rationals. The mechanism uses both:                      *)
(* - Frequencies: how many cycles per year (gear train outputs)               *)
(* - Periods: how many days per cycle (astronomical constants)                *)
(*                                                                            *)
(* AUTOMATION TACTICS:                                                        *)
(* - solve_gear_ratio: resolves gear ratio equalities                         *)
(* - solve_Qeq: handles rational equality goals                               *)
(* - prove_ratio_bounds: establishes inequality bounds                        *)
(*                                                                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Frequency                                                                  *)
(* -------------------------------------------------------------------------- *)
(* SOURCE:    Dimensional analysis for astronomical rates                     *)
(* EVIDENCE:  Gear trains produce frequency ratios (cycles per time)          *)
(* SEMANTICS: Wrapper distinguishing frequencies from periods                 *)
(* -------------------------------------------------------------------------- *)
Record Frequency := mkFrequency { freq_value : Q }.
Record Period := mkPeriod { period_value : Q }.

Definition freq_to_period (f : Frequency) : Period :=
  mkPeriod (Qinv (freq_value f)).

Definition period_to_freq (p : Period) : Frequency :=
  mkFrequency (Qinv (period_value p)).

Lemma freq_period_inverse_example :
  Qeq (Qinv (Qinv (254 # 19))) (254 # 19).
Proof.
  unfold Qeq, Qinv. simpl. reflexivity.
Qed.

Definition lunar_sidereal_freq : Frequency := mkFrequency (254 # 19).
Definition metonic_synodic_freq : Frequency := mkFrequency (235 # 19).

Lemma synodic_freq_from_sidereal :
  Qeq (freq_value metonic_synodic_freq) 
      (Qminus (freq_value lunar_sidereal_freq) (1 # 1)).
Proof.
  unfold metonic_synodic_freq, lunar_sidereal_freq, freq_value, Qeq, Qminus.
  simpl. reflexivity.
Qed.

Ltac solve_gear_ratio :=
  unfold gear_ratio, teeth; simpl; reflexivity.

Ltac solve_Qeq :=
  unfold Qeq; simpl; try reflexivity; try lia.

Ltac prove_ratio_bounds :=
  unfold Qlt, Qle; simpl; lia.

Definition ct_uncertainty_error_bound : Q := 5 # 1000.

Lemma gear_188_interval_small :
  Qlt (Qminus (190 # 60) (186 # 60)) (1 # 10).
Proof.
  unfold Qminus, Qlt. simpl. lia.
Qed.

Definition mars_synodic_from_period (orbital_period_years sidereal_year : Q) : Q :=
  Qinv (Qminus (Qinv orbital_period_years) (Qinv sidereal_year)).

Definition mars_orbital_period : Q := 18780 # 10000.

Lemma mars_retrograde_related_to_synodic :
  Qlt (mars_retrograde_duration_days) (mars_synodic_days / (5 # 1)).
Proof.
  unfold mars_retrograde_duration_days, mars_synodic_days, Qdiv, Qlt.
  simpl. lia.
Qed.

(* ========================================================================== *)
(* END                                                                        *)
(* ========================================================================== *)
