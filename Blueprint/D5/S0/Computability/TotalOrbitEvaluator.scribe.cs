using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class TotalOrbitEvaluatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No computable total function evaluates every partial-recursive code at every input.",
        H("No Total Evaluator for Program Orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-computable-total-orbit-evaluator"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/TotalOrbitEvaluator.no_computable_total_orbit_evaluator"),
                H("A computable total orbit evaluator cannot exist"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Exists, Sp, F.Id("V"), Colon, Sp,
                    Operatorname, Grp(F.Id("Code")), To, Sp,
                    Mathbb, Grp(F.Id("N")), To, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("Computable")), Underscore, D(2),
                    Open, F.Id("V"), Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("c"), Comma, Sp, F.Id("n"), Comma, Sp,
                    Operatorname, Grp(F.Id("eval")), Open, F.Id("c"), Comma, Sp,
                    F.Id("n"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("some")), Open, F.Id("V"), Open,
                    F.Id("c"), Comma, Sp, F.Id("n"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The claim quantifies over total functions from a program code and a "
                        + "natural input to a natural output. It excludes precisely those "
                        + "functions that are computable and agree, through Part.some, with the "
                        + "partial "
                        + "evaluation of every code at every input. Both the code type and the "
                        + "total function type are inhabited; the theorem has no external "
                        + "hypotheses, so hypothesis satisfiability is vacuous rather than hidden "
                        + "in an empty domain.")),
                    Paragraph(Text(
                        "This is an honest partial closure of clause (iii) of the source theorem. "
                        + "The output swap is instantiated by successor, a computable map with no "
                        + "fixed natural number. Clauses (i) and (ii), concerning predicate "
                        + "enumeration and binary streams, remain unresolved by this deposit and "
                        + "the source atom must therefore remain partial and open.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. Function.cantor_surjective is "
                        + "an exact hit for clause (i). Nat.Partrec.Code.fixed_point and the "
                        + "existing code_fixed_point wrapper were found but are unary. "
                        + "Nat.Partrec.Code.fixed_point2 was queried under its rendered library "
                        + "name "
                        + "and found as the exact binary fixed-point engine; "
                        + "Nat.Partrec.Code.eval_part and Computable.succ were also found. The "
                        + "related closure_reading_unreachable declaration was inspected, but no "
                        + "exact universal-total-evaluator theorem was found.")),
                    Paragraph(Text(
                        "The proof forms successor of the proposed evaluator as a binary partial "
                        + "recursive function. The library fixed-point theorem supplies a code "
                        + "whose behavior equals that diagonal function. Specializing the equality "
                        + "at zero and rewriting with the evaluator premise forces a natural "
                        + "number to equal its successor."))),
                DescribeRole.Theorem))));
}
