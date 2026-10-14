using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AntidistinguishabilityOverlapNonTightDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/johnstonrussosikora2025antidistinguishability");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional spectral and overlap bounds for antidistinguishability.",
        H("AntidistinguishabilityOverlapNonTight"), Blocks(
            Describe.Lean(DescribeId.Create("istight"),
                DeclarationHandle.Create(Owner + ".IsTight"), H("IsTight"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Section 6, page 17: “We still do not know whether or not Corollary 5.4 is tight when n ≥ 5.” The displayed tightness condition uses a squared-overlap margin. For n ≥ 10 the source cap is positive, so squaring reparametrizes its positive margin."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Owner + ".claim"), H("claim"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("Section 6, page 17: “We still do not know whether or not Corollary 5.4 is tight when n ≥ 5.” The statement answers the question by proving non-tightness for every n ≥ 10; n = 5,…,9 remain open."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitative-antidistinguishability"),
                DeclarationHandle.Create(Owner + ".quantitative_antidistinguishability"), H("quantitative antidistinguishability"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Owner + ".result"), H("result"),
                StatementSource.FromAuthor(Disp(Formula3())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("johnston-russo-sikora-2025-antidistinguishability-tightness"),
                    ResolutionKind.Proved)))));

    private static Formula Formula0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("IsTight"), Sp, F.Id("n"), Sp, Eq, Sp, Forall, Sp, Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Comma, Sp, Varepsilon, Sp, Gt, Sp, D(0), Sp, To, Sp, Exists, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Vert, Sp, Psi, Sp, F.Id("i"), Sp, Vert, Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, To, Sp, Vert, Sp, F.Id("inner"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(Psi, Sp, F.Id("i"))), Sp, Parenthesized(Seq(Psi, Sp, F.Id("j"))), Sp, new Formula.Power(Vert, D(2)), Sp, Leq, Sp, F.Id("cSq"), Sp, F.Id("n"), Sp, Plus, Sp, Varepsilon)), Sp, Land, Sp, Neg, Sp, F.Id("IsAntidistinguishable"), Sp, Psi);

    private static Formula Formula1() =>
        Seq(F.Id("claim"), Sp, Eq, Sp, Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1,0), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Neg, Sp, F.Id("IsTight"), Sp, F.Id("n"));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(1,0), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Vert, Sp, Psi, Sp, F.Id("i"), Sp, Vert, Sp, Eq, Sp, D(1))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, To, Sp, Vert, Sp, F.Id("inner"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(Psi, Sp, F.Id("i"))), Sp, Parenthesized(Seq(Psi, Sp, F.Id("j"))), Sp, new Formula.Power(Vert, D(2)), Sp, Leq, Sp, F.Id("cSq"), Sp, F.Id("n"), Sp, Plus, Sp, F.Id("delta"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("IsAntidistinguishable"), Sp, Psi);

    private static Formula Formula3() =>
        F.Id("claim");
}
