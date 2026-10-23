import Lean

namespace LeanInformationAudit.SearchReduction
open Lean

abbrev certificateLanguageVersion : String := "obvious/v1/name-only"

/-- Untrusted data. There is deliberately no expression, tactic, witness,
instance, attribute, direction or lemma-list field. -/
inductive ObviousCertificate where
  | close
  | lookup (name : Name)
  | member (name : Name)
  deriving Inhabited, Repr, DecidableEq

declare_syntax_cat obvious_certificate
syntax "by_close" : obvious_certificate
syntax "by_lookup " ident : obvious_certificate
syntax "by_member " ident : obvious_certificate

def parseObviousCertificate (stx : TSyntax `obvious_certificate) : Except String ObviousCertificate :=
  match stx with
  | `(obvious_certificate| by_close) => .ok .close
  | `(obvious_certificate| by_lookup $name:ident) => .ok (.lookup name.getId)
  | `(obvious_certificate| by_member $name:ident) => .ok (.member name.getId)
  | _ => .error "certificate.invalid_syntax"

def ObviousCertificate.render : ObviousCertificate → String
  | .close => "by_close"
  | .lookup name => s!"by_lookup {name}"
  | .member name => s!"by_member {name}"

/-- A label is provenance only; it never supplies evidence of failure. -/
structure CertificateNomination where
  certificate : ObviousCertificate
  provenance : String
  deriving Inhabited, Repr, DecidableEq

end LeanInformationAudit.SearchReduction
