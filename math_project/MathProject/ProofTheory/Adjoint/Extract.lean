/-- The property of taking one element from L and calculating the remainder without x. -/
class inductive Extract {α : Type} (x : α) : List α → outParam (List α) → Type where
| head {xs : List α} : Extract x (x :: xs) xs
| there {y : α} {xs ys : List α} (ext : Extract x xs ys) : Extract x (y :: xs) (y :: ys)

/-- obtain L' with Extract x L L' -/
def Extract.extract {α : Type} (x : α) (L : List α) {L' : List α} [Extract x L L'] : List α := L'

/-- obtain x :: L' with Extract x L L' -/
def Extract.cons {α : Type} (x : α) (L : List α) {L' : List α} [Extract x L L'] : List α := x :: L'

instance instExtractHead {α : Type} {x : α} {xs : List α} :
  Extract x (x :: xs) xs := Extract.head

instance instExtractThere {α : Type} {x y : α} {xs ys : List α} [Extract x xs ys] :
  Extract x (y :: xs) (y :: ys) := Extract.there inferInstance

instance instExtractAppendLeft {α : Type} {x : α} {L₁ L₁' L₂ : List α}
  [ext : Extract x L₁ L₁'] : Extract x (L₁ ++ L₂) (L₁' ++ L₂) :=
  match ext with
  | .head => .head
  | .there ext => .there instExtractAppendLeft

instance instExtractAppendRight {α : Type} {y : α} {L₁ L₂ L₂' : List α}
  [ext : Extract y L₂ L₂'] : Extract y (L₁ ++ L₂) (L₁ ++ L₂') :=
  match L₁ with
  | [] => ext
  | _ :: _ => .there instExtractAppendRight

open Extract

#eval extract 3 [1, 2, 3, 4]
-- >> [1, 2, 4]

#eval cons 3 [1, 2, 3, 4]
-- >> [3, 1, 2, 4]

#eval extract 3 ([1, 2] ++ [3, 4])
-- >> [1, 2, 4]

#eval cons 3 ([1, 2] ++ [3, 4])
-- >> [3, 1, 2, 4]

/-- The property of taking a subList from L and calculating the remainder. -/
class inductive ExtractList {α : Type} : List α → List α → outParam (List α) → Type where
| nil {L : List α} : ExtractList [] L L
| cons {x : α} {xs L L' L'' : List α}
  [ext : Extract x L L'] (extl : ExtractList xs L' L'') : ExtractList (x :: xs) L L''

/-- obtain L₂ with ExtractList L₁ L L₂ -/
def ExtractList.extractlist {α : Type} (L₁ L : List α) {L₂ : List α} [ExtractList L₁ L L₂] : List α := L₂

instance instExtractListNil {α : Type} {L : List α} : ExtractList [] L L := ExtractList.nil

instance instExtractListCons {α : Type} {x : α} {xs L L' L'' : List α}
  [ext : Extract x L L'] [extl : ExtractList xs L' L''] :
  ExtractList (x :: xs) L L'' := ExtractList.cons inferInstance

instance instExtractListAppendLeft {α : Type} (L₁ : List α) {L₂ : List α} : ExtractList L₁ (L₁ ++ L₂) L₂ :=
  match L₁ with
  | [] => ExtractList.nil
  | _ :: xs => ExtractList.cons (instExtractListAppendLeft xs)

instance instExtractListAppendRight {α : Type} {L₁ : List α} (L₂ : List α) : ExtractList L₂ (L₁ ++ L₂) L₁ :=
  match L₂ with
  | [] => by rw [List.append_nil]; exact ExtractList.nil
  | _ :: ys => ExtractList.cons (instExtractListAppendRight ys)

instance instExtractListAppend {α : Type} {L₁ L₂ L L' L'' : List α} :
  [ExtractList L₁ L L'] → [ExtractList L₂ L' L''] → ExtractList (L₁ ++ L₂) L L''
  | .nil, _ => by rw [List.nil_append]; trivial
  | .cons (ext := ext) extl, _ => ExtractList.cons (ext := ext) instExtractListAppend

/-- Extract x L L' → ExtractList [x] L L' -/
instance instExtractListSingletonFromExtract {α : Type} {x : α} {L L' : List α}
  [ext : Extract x L L'] :
  ExtractList [x] L L' := ExtractList.cons ExtractList.nil

/-- ExtractList [x] L L' → Extract x L L₁ -/
instance instExtractFromExtractListSingleton {α : Type} {x : α} {L L' : List α}
  [extl : ExtractList [x] L L'] : Extract x L L' := by
  cases extl with
  | cons h' => cases h'; assumption

open ExtractList

#eval extractlist [2, 4] [1, 2, 3, 4]
-- >> [1, 3]

#eval extractlist [1, 2] ([1, 2] ++ [3, 4])
-- >> [3, 4]

#eval extractlist [3, 4] ([1, 2] ++ [3, 4])
-- >> [3, 4]

#eval extractlist [2, 4] ([1, 2] ++ [3, 4])
-- >> [1, 3]

#eval extractlist [1, 3] ([1, 2] ++ [3, 4])
-- >> [2, 4]

#eval extractlist ([2] ++ [4]) [1, 2, 3, 4]
-- >> [1, 3]

#eval extractlist ([4] ++ [2]) [1, 2, 3, 4]
-- >> [1, 3]

/-- reflection for ExtractList -/
@[instance_reducible]
def extractList_refl {α : Type} : {L : List α} → ExtractList L L []
| [] => .nil
| _ :: _ => .cons (ext := .head) (extractList_refl)

/-- Extract y Γ Γ' → Extract x Γ' Γ'' → Σ Γ', Extract x Γ Γ' × Extract y Γ' Γ'' -/
def Extract.comm {α : Type} {x y : α} {Γ Γ' Γ'' : List α}
  (ext_y : Extract y Γ Γ') (ext_x : Extract x Γ' Γ'') :
  Σ Γ', Extract x Γ Γ' × Extract y Γ' Γ'' :=
  match ext_y with
  | .head => ⟨_, Extract.there ext_x, Extract.head⟩
  | .there ext =>
    match ext_x with
    | .head => ⟨_, Extract.head, ext⟩
    | .there hx' =>
      let ⟨_, h1, h2⟩ := Extract.comm ext hx'
      ⟨_, Extract.there h1, Extract.there h2⟩

/-- (Extract x L₁ L') → (ExtractList L₁ L₂ []) → Σ L'', Extract x L₂ L'' -/
def extract_of_extractList {α : Type} {x : α} {L₁ L₂ L' : List α} :
(Extract x L₁ L') → (ExtractList L₁ L₂ []) → Σ L'', Extract x L₂ L'' × ExtractList L' L'' []
| .head, .cons (ext := ext) extl => ⟨_, ext, extl⟩
| .there ext, .cons (ext := ext') extl =>
  let ⟨_, ext_x, extl'⟩ := extract_of_extractList ext extl
  let ⟨_, hx', hy'⟩ := Extract.comm ext' ext_x
  ⟨_, hx', .cons (ext := hy') extl'⟩

/-- transition for ExtractList -/
@[instance_reducible]
def extractList_trans {α : Type} :
{L₁ L₂ L₃ : List α} → (ExtractList L₁ L₂ []) → (ExtractList L₂ L₃ []) → ExtractList L₁ L₃ []
| _, _, _, .nil, _ => by trivial
| _, _, _, .cons (ext := ext) extl, extl' =>
  let ⟨_, ext', extl''⟩ := extract_of_extractList ext extl'
  let ih := extractList_trans extl extl''
  .cons (ext := ext') ih

/-- Extract x L L' → ExtractList L (x :: L') [] -/
@[instance_reducible]
def extractList_of_extract {α : Type} {x : α} {L L' : List α} :
(Extract x L L') → ExtractList L (x :: L') []
| .head => extractList_refl
| .there ext_tail => .cons (extractList_of_extract ext_tail)

/-- symmetry for ExtractList -/
@[instance_reducible]
def extractList_symm {α : Type} :
{L₁ L₂ : List α} → (ExtractList L₁ L₂ []) → ExtractList L₂ L₁ []
| _, _, .nil => .nil
| _, _, .cons (ext := ext) extl =>
  let ih := extractList_symm extl
  extractList_trans (extractList_of_extract ext) (.cons (ext := .head) ih)
