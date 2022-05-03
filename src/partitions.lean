
import syntax
import tableau
import semantics

open hasVocabulary

def partition (X : finset formula) := { L | L ⊆ X }

def partedTableau {X} : Type := closedTableau X × partition X

def partedLocalTableau {X} : Type := localTableau X × partition X

def L {X} : partition X → finset formula | p := p
def R {X} : partition X → finset formula | p := X \ p

-- Definition 24
def part_interpolant {X : finset formula} (p : partition X) (θ : formula) :=
  voc θ ⊆ (voc (L p) ∩ voc (R p))
  ∧
  inconsistent ( L p ∪ {~θ} )
  ∧
  inconsistent ( R p ∪ {θ} )
