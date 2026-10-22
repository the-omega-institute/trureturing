using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OverlapLowRankDistanceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/OverlapLowRankDistance";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/johnstonrussosikora2025antidistinguishability");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional spectral and overlap bounds for antidistinguishability.",
        H("OverlapLowRankDistance"), Blocks(
            Describe.Lean(DescribeId.Create("eigenvalue-lower-of-psd-sub-scalar"),
                DeclarationHandle.Create(Owner + ".eigenvalue_lower_of_psd_sub_scalar"),
                H("A scalar lower bound for every eigenvalue"),
                StatementSource.FromAuthor(Disp(EigenvalueLowerFormula())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("For a Hermitian matrix A on an arbitrary finite index type, positive semidefiniteness of A minus a times the identity implies that every eigenvalue of A is at least a. Evaluate the quadratic form on a unit eigenvector. The index type may be empty, in which case the conclusion has no instances."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("csq-nonneg"),
                DeclarationHandle.Create(Owner + ".cSq_nonneg"), H("cSq nonneg"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("delta-budget"),
                DeclarationHandle.Create(Owner + ".delta_budget"), H("delta budget"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("frobsq-add-le-twice"),
                DeclarationHandle.Create(Owner + ".frobSq_add_le_twice"), H("frobSq add le twice"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("delta-pos"),
                DeclarationHandle.Create(Owner + ".delta_pos"), H("delta pos"),
                StatementSource.FromAuthor(Disp(Formula3())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("csq-lt-half"),
                DeclarationHandle.Create(Owner + ".cSq_lt_half"), H("cSq lt half"),
                StatementSource.FromAuthor(Disp(Formula4())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("offdiag-card"),
                DeclarationHandle.Create(Owner + ".offDiag_card"), H("offDiag card"),
                StatementSource.FromAuthor(Disp(Formula5())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equaloverlap"),
                DeclarationHandle.Create(Owner + ".equalOverlap"), H("equalOverlap"),
                StatementSource.FromAuthor(Disp(Formula6())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete definition. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("low-rank-distance-lower"),
                DeclarationHandle.Create(Owner + ".low_rank_distance_lower"), H("low rank distance lower"),
                StatementSource.FromAuthor(Disp(Formula7())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("delta-overlap-budget"),
                DeclarationHandle.Create(Owner + ".delta_overlap_budget"), H("delta overlap budget"),
                StatementSource.FromAuthor(Disp(Formula8())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-rank-contradiction"),
                DeclarationHandle.Create(Owner + ".quantitative_rank_contradiction"), H("quantitative rank contradiction"),
                StatementSource.FromAuthor(Disp(Formula9())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlap-excess-identity"),
                DeclarationHandle.Create(Owner + ".overlap_excess_identity"), H("overlap excess identity"),
                StatementSource.FromAuthor(Disp(Formula10())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equaloverlap-low-rank-distance"),
                DeclarationHandle.Create(Owner + ".equalOverlap_low_rank_distance"), H("equalOverlap low rank distance"),
                StatementSource.FromAuthor(Disp(Formula11())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlap-target-distance-bound"),
                DeclarationHandle.Create(Owner + ".overlap_target_distance_bound"), H("overlap target distance bound"),
                StatementSource.FromAuthor(Disp(Formula12())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem))));

    private static Formula EigenvalueLowerFormula()
    {
        var index = F.Id("I");
        var a = F.Id("a");
        var matrix = F.Id("A");
        var h = F.Id("h");
        Formula Apply(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
        Formula All(string name, Formula type, Formula body) =>
            Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
        Formula Property(Formula value, string name) => Seq(Parenthesized(value), Dot, F.Id(name));
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var shift = Seq(matrix, Sp, Minus, Sp, a, Sp, Cdot, Sp,
            Parenthesized(Seq(D(1), Sp, Colon, Sp, Apply("Matrix", index, index, complex))));
        var eigenvalue = new Formula.Apply(Property(h, "eigenvalues"), [F.Id("i")]);
        return All("I", F.Id("Type"), Seq(
            OpenBracket, Apply("Fintype", index), CloseBracket, Sp,
            OpenBracket, Apply("DecidableEq", index), CloseBracket, Comma, Sp,
            All("A", Apply("Matrix", index, index, complex),
                All("h", Property(matrix, "IsHermitian"), All("a", real,
                    Seq(Property(shift, "PosSemidef"), Sp, Implies, Sp,
                        All("i", index, Seq(a, Sp, Leq, Sp, eigenvalue)))))));
    }

    private static Formula Formula0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, D(0), Sp, Leq, Sp, F.Id("cSq"), Sp, F.Id("n"));

    private static Formula Formula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1,0), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(3))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))))), Sp, Cdot, Sp, F.Id("delta"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Slash, Sp, D(1,6));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Plus, Sp, F.Id("B"))), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, F.Id("A"), Sp, Plus, Sp, D(2), Sp, Cdot, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, F.Id("B"));

    private static Formula Formula3() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1,0), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, D(0), Sp, Lt, Sp, F.Id("delta"), Sp, F.Id("n"));

    private static Formula Formula4() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, F.Id("cSq"), Sp, F.Id("n"), Sp, Lt, Sp, D(1), Sp, Slash, Sp, D(2));

    private static Formula Formula5() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(F.Id("univ"), Sp, Colon, Sp, F.Id("Finset"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))), Sp, Dot, Sp, F.Id("offDiag")))), Sp, Dot, Sp, F.Id("card"), Sp, Eq, Sp, F.Id("n"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Minus, Sp, D(1))));

    private static Formula Formula6() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, F.Id("equalOverlap"), Sp, F.Id("n"), Sp, F.Id("c"), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("c"))), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Plus, Sp, F.Id("c"), Sp, Cdot, Sp, F.Id("Matrix"), Sp, Dot, Sp, F.Id("of"), Sp, Parenthesized(Seq(F.Id("Function"), Sp, Dot, Sp, F.Id("const"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Function"), Sp, Dot, Sp, F.Id("const"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))))));

    private static Formula Formula7() =>
        Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, F.Id("Type"))), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, Iota), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, Iota), CloseBracket), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, F.Id("B"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("B"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Leq, Sp, F.Id("a"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp, Comma, Sp, F.Id("a"), Sp, Leq, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("i"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("B"), Sp, Dot, Sp, F.Id("rank"), Sp, Leq, Sp, F.Id("r"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Iota, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, F.Id("r"))), Sp, Cdot, Sp, new Formula.Power(F.Id("a"), D(2)), Sp, Leq, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Minus, Sp, F.Id("B"))));

    private static Formula Formula8() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1,0), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, new Formula.Power(Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))))), Sp, Cdot, Sp, F.Id("delta"), Sp, F.Id("n"))), D(2)), Sp, Leq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Slash, Sp, D(6,4));

    private static Formula Formula9() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1,0), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("dist2"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("dist2"), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Slash, Sp, D(1,6))), Sp, Plus, Sp, D(2), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Slash, Sp, D(6,4))))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("cSq"), Sp, F.Id("n"))), D(2)), Sp, Leq, Sp, F.Id("dist2"))), Sp, To, Sp, F.Id("False"));

    private static Formula Formula10() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("G"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, Eq, Sp, D(1))), Sp, To, Sp, Parenthesized(Seq(Sum, Sp, F.Id("p"), Sp, InMacro, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("univ"), Sp, Colon, Sp, F.Id("Finset"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))), Sp, Dot, Sp, F.Id("offDiag"))), Sp, Comma, Sp, Parenthesized(Seq(Vert, Sp, F.Id("G"), Sp, F.Id("p"), Sp, Dot, Sp, D(1), Sp, F.Id("p"), Sp, Dot, Sp, D(2), Sp, new Formula.Power(Vert, D(2)), Sp, Minus, Sp, F.Id("cSq"), Sp, F.Id("n"))))), Sp, Eq, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, F.Id("G"), Sp, Minus, Sp, new Formula.Power(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), D(2)), Sp, Slash, Sp, D(2));

    private static Formula Formula11() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Leq, Sp, F.Id("c"))), Sp, To, Sp, Parenthesized(Seq(F.Id("c"), Sp, Leq, Sp, D(1))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("B"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, To, Sp, Parenthesized(Seq(F.Id("B"), Sp, Dot, Sp, F.Id("rank"), Sp, Leq, Sp, F.Id("r"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, F.Id("r"))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("c"))), D(2)), Sp, Leq, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, Parenthesized(Seq(F.Id("equalOverlap"), Sp, F.Id("n"), Sp, F.Id("c"), Sp, Minus, Sp, F.Id("B"))));

    private static Formula Formula12() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("G"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, Eq, Sp, D(1))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Leq, Sp, F.Id("e"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, To, Sp, Vert, Sp, F.Id("G"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, new Formula.Power(Vert, D(2)), Sp, Leq, Sp, F.Id("cSq"), Sp, F.Id("n"), Sp, Plus, Sp, F.Id("e"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Leq, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, F.Id("G"), Sp, Minus, Sp, new Formula.Power(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), D(2)), Sp, Slash, Sp, D(2))), Sp, To, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("frobSq"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("normSqMatrix"), Sp, F.Id("G"))), Sp, Dot, Sp, F.Id("map"), Sp, Parenthesized(Seq(F.Id("algebraMap"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Minus, Sp, F.Id("equalOverlap"), Sp, F.Id("n"), Sp, Parenthesized(Seq(F.Id("cSq"), Sp, F.Id("n"))))), Sp, Leq, Sp, new Formula.Power(Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))))), Sp, Cdot, Sp, F.Id("e"))), D(2)));
}
