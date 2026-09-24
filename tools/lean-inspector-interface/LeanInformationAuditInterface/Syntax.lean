import Lean

namespace LeanInformationAudit

open Lean

/-- Command dispatch also considers identifiers, without reserving the spelling. -/
def expect_information_occurrenceKeyword : Parser.Parser := Parser.nonReservedSymbol "expect_information_occurrence" true
def information_theoremKeyword : Parser.Parser := Parser.nonReservedSymbol "information_theorem" true
def register_information_theoremKeyword : Parser.Parser := Parser.nonReservedSymbol "register_information_theorem" true
def register_information_templateKeyword : Parser.Parser := Parser.nonReservedSymbol "register_information_template" true
def declare_information_template_bindingKeyword : Parser.Parser := Parser.nonReservedSymbol "declare_information_template_binding" true
def informationInlineKeyword : Parser.Parser := Parser.nonReservedSymbol "inline" true

/-- Clause delimiters are tokens only while reading the preceding registration
term. They never enter an importing module's global identifier vocabulary. -/
def registrationTerm : Parser.Parser := {
  Parser.termParser with
  fn := Parser.adaptUncacheableContextFn (fun context =>
    { context with tokens := (#["realization", "variation", "sensitivity", "output_evidence", "escape"].foldl
        (fun tokens word => tokens.insert word word) context.tokens) }) Parser.termParser.fn }

@[combinator_formatter registrationTerm]
def registrationTermFormatter : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.categoryParser.formatter `term
@[combinator_parenthesizer registrationTerm]
def registrationTermParenthesizer : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.categoryParser.parenthesizer `term 0

declare_syntax_cat informationRealization
syntax (name := namedInformationRealization) ident : informationRealization
syntax (name := inlineInformationRealization) (priority := high)
  informationInlineKeyword registrationTerm " := " registrationTerm : informationRealization

/-- Preserve the group nodes inserted by the original combined `elab` forms. -/
-- Declare one independently expected auxiliary-root occurrence.
syntax (name := command___In__From_)
  group(expect_information_occurrenceKeyword) ident group(ppLine)
    &"in " ident group(ppLine)
    &"from " str : command

/-- Negative-fixture form for pinning an independently supplied statement identity. -/
syntax (name := command___In__From__Statement_id_)
  group(expect_information_occurrenceKeyword) ident group(ppLine)
    &"in " ident group(ppLine)
    &"from " str group(ppLine)
    &"statement_id " str : command

syntax (name := informationTheoremCmd)
  information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"primitives " registrationTerm ppLine
    (&"variation " ident)? (&"sensitivity " ident)?
    ": " term " := " term : command

syntax (name := registerInformationTheoremCmd)
  register_information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"primitives " registrationTerm &" realization " informationRealization
    (&" variation " ident)? (&" sensitivity " ident)? : command

syntax (name := registerInformationTheoremViaCmd)
  register_information_theoremKeyword ident &" via " term &" in " ident (&" output_evidence " term)? : command

syntax (name := informationTheoremOccurrenceCmd)
  information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"object_arena " ident ppLine
    &"catalog " ident ppLine
    &"primitives " registrationTerm ppLine
    (&"variation " ident)? (&"sensitivity " ident)?
    ": " term " := " term : command

syntax (name := registerInformationTheoremOccurrenceCmd)
  register_information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"object_arena " ident ppLine
    &"catalog " ident ppLine
    &"primitives " registrationTerm &" realization " informationRealization
    (&" variation " ident)? (&" sensitivity " ident)? : command

syntax (name := command__)
  group(register_information_templateKeyword) ident : command

syntax (name := «command__Constructors_[_,,]»)
  group(register_information_templateKeyword) ident &" constructors " num
    " [" ident,* "]" : command

declare_syntax_cat informationEscapeContinuation
syntax (name := escapeOpenContinuation) &"open" : informationEscapeContinuation
syntax (name := escapeCertifiedContinuation) term : informationEscapeContinuation

syntax (name := registerInformationTheoremReadoutCmd)
  register_information_theoremKeyword ident &" in " ident
  &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  &" realization " informationRealization
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

syntax (name := registerInformationTheoremViaReadoutCmd)
  register_information_theoremKeyword ident &" via " term &" in " ident
  &"readout " &"via " "(" term ")" (&" output_evidence " registrationTerm)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

syntax (name := registerInformationTheoremOccurrenceReadoutCmd)
  register_information_theoremKeyword ident &" in " ident &" object_arena " ident &" catalog " ident
  &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  &" realization " informationRealization
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

syntax (name := informationTheoremReadoutCmd)
  information_theoremKeyword ident &" in " ident &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? ": " term " := " term : command

syntax (name := informationTheoremOccurrenceReadoutCmd)
  information_theoremKeyword ident &" in " ident &" object_arena " ident &" catalog " ident
  &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? ": " term " := " term : command

syntax (name := declareInformationTemplateBindingCmd)
  declare_information_template_bindingKeyword ident &" in " ident
  (&" object_arena " ident &" catalog " ident)? &"readout " &"via " "(" term ")"
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

end LeanInformationAudit
