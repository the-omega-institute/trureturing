using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedResponsePresburgerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Computed Presburger formulas realize fixed paths and final-update crossings exactly.",
        H("Fixed Response Presburger Formulas"),
        Blocks(
            Describe.Lean(DescribeId.Create("progression-formula"), Handle("progressionFormula"),
                H("Computed constants and one quantified variable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For natural coefficients a and C, the formula has one free count variable d. "
                    + "If C is zero it is d equals a. Otherwise it is exists m, d equals a plus "
                    + "C times m, with C times m represented by repeated addition. These are "
                    + "actual Mathlib Language.presburger terms and bounded formulas."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-list-formula"), Handle("pathListFormula"),
                H("Endpoint-filtered finite disjunction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A list fold joins the progression formulas whose actual endpoints equal "
                    + "the requested control y. All other records contribute false. An empty "
                    + "list gives false. No choice-based finite-set conversion or sum is used."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("crossing-list-formula"), Handle("crossingListFormula"),
                H("The final edge must be a genuine update"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a record ending at some z, inspect the same table at z. Retain it "
                    + "only if that instruction is update y, and increase its offset by one. "
                    + "Read and halt endpoints and the sink contribute false. Positive path "
                    + "weight alone is insufficient: a path ending after reads need not cross "
                    + "by an update into that endpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-formula"), Handle("pathFormula"),
                H("Fixed-response path syntax"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Construct the finite endpoint records for the supplied table, response "
                    + "field and initial control, then fold their endpoint-filtered formulas. "
                    + "The output is executable syntax with one free natural count variable."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("crossing-formula"), Handle("crossingFormula"),
                H("Final-update crossing syntax"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Use the same computed records and the same table to construct the "
                    + "disjunction over real final-update predecessors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-formula-realization"), Handle("fixed_response_formulas_correct"),
                H("Exact realization of both native relations"), StatementSource.FromAuthor(ExactFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "For every finite control type with explicit Fintype and DecidableEq "
                        + "instances, arbitrary address and reply types, program f, response "
                        + "field v, controls x and y, and natural count d, realization of the "
                        + "path formula at d is equivalent to FixedPath f v x y d, and "
                        + "realization of the crossing formula at d is equivalent to "
                        + "Crossing f v x y d. Both conjuncts use the same program and vector.")),
                    Paragraph(Text(
                        "Mathlib realizes computed numerals and natural scalar multiples "
                        + "as their natural arithmetic values. Mathlib's realization theorem "
                        + "for list disjunctions identifies the fold with finite progression support. "
                        + "The exact native-path support theorem supplies both directions. "
                        + "For crossing, the retained predecessor supplies the real final "
                        + "update constructor, and the offset shift records its unit weight.")),
                    Paragraph(Text(
                        "Zero-weight cycles collapse to singleton weights while retaining "
                        + "endpoints. Empty paths and transient halt endpoints remain reachable; "
                        + "a halt has no final outgoing update. The theorem quantifies over "
                        + "every natural count without imposing an instruction or update bound.")),
                    Paragraph(Text(
                        "This completes the fixed-response arithmetic component. Synthesis "
                        + "of the shared-source guards, effective rank and descriptor formulas, "
                        + "and their full phase composition are separate obligations. The "
                        + "definitions do not assert a uniform Computable theorem for an "
                        + "external program encoding. No literature novelty is asserted."))), DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => Seq(args.SelectMany((arg, i) =>
        i == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray());

    private static Formula ExactFormula()
    {
        Formula q = F.Id("Q"), a = F.Id("A"), r = F.Id("R"),
            f = F.Id("f"), v = F.Id("v"), x = F.Id("x"), y = F.Id("y"), d = F.Id("d");
        Formula realization(string compiler) => Call("Realize", Call(compiler, f, v, x, y),
            Seq(Operatorname, Grp(F.Id("const")), Open, d, Close));
        return Disp(Seq(Forall, Sp, q, Comma, Sp, a, Comma, Sp, r, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("Fintype", q), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", q), CloseBracket, Comma, Esc,
            Forall, Sp, f, Colon, Sp, q, Sp, To, Sp, Call("Instruction", q, a, r), Comma, Sp,
            v, Colon, Sp, a, Sp, To, Sp, r, Comma, Esc,
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, q, Comma, Sp,
            d, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Open, realization("pathFormula"), Sp, Iff, Sp, Call("FixedPath", f, v, x, y, d), Close,
            Sp, Land, Esc,
            Open, realization("crossingFormula"), Sp, Iff, Sp, Call("Crossing", f, v, x, y, d), Close));
    }
}
