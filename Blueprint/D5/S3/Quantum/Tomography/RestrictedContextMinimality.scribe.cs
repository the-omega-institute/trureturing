using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class RestrictedContextMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete complementary-context family is minimal among its context subfamilies.",
        H("Restricted Context Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("restricted-context-readout"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/RestrictedContextMinimality."
                        + "restrictedContextReadout"),
                H("Restricted context readout"),
                StatementSource.FromAuthor(ReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite subfamily S of the supplied contexts, the readout retains "
                        + "exactly the projector-trace coordinates indexed by S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("omitted-context-projectors-indistinguishable"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/RestrictedContextMinimality."
                        + "omitted_context_projectors_indistinguishable"),
                H("An omitted context supplies indistinguishable projectors"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In dimension n+1 at least two, assume the complete complementary "
                            + "overlap law. If context ell is absent from S, its outcome-zero "
                            + "and outcome-one projectors are distinct but every retained "
                            + "context gives them the same trace coordinates.")),
                    Paragraph(Text(
                        "The two matrices are explicit and uniform for every omitted context; "
                            + "no positivity or density-state premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("restricted-context-readout-injective-iff"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/RestrictedContextMinimality."
                        + "restricted_contextReadout_injective_iff"),
                H("Exact classification of injective context subfamilies"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same dimension and overlap hypotheses, the restricted "
                            + "readout is injective on the full complex matrix carrier exactly "
                            + "when S is the full finite context family.")),
                    Paragraph(Text(
                        "The forward obstruction uses the explicit omitted-context pair; the "
                            + "reverse implication reuses complete context tomography."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula MatrixType(Formula n) =>
        Call("Matrix", Fin(Seq(n, F.Plus, F.D(1))),
            Fin(Seq(n, F.Plus, F.D(1))), Seq(F.Mathbb, F.Grp(F.Id("C"))));

    private static Formula ContextType(Formula n) =>
        Arrow(Fin(Seq(n, F.Plus, F.D(2))),
            Call("RankOneContext", Seq(n, F.Plus, F.D(1))));

    private static Formula Projector(Formula context, Formula ell, Formula j) =>
        Call("projector", context, ell, j);

    private static Formula ReadoutFormula()
    {
        Formula n = F.Id("n");
        Formula context = F.Id("C");
        Formula subset = F.Id("S");
        Formula matrix = F.Id("X");
        Formula ell = F.Id("ell");
        Formula j = F.Id("j");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, n, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Sp,
            context, F.Colon, F.Sp, ContextType(n), F.Comma, F.Sp,
            subset, F.Colon, F.Sp, Call("Finset", Fin(F.Seq(n, F.Plus, F.D(2)))), F.Comma,
            F.RowBreak, F.Grp(), matrix, F.Colon, F.Sp, MatrixType(n), F.Comma, F.Sp,
            ell, F.InMacro, F.Sp, subset, F.Comma, F.Sp, j, F.InMacro, F.Sp, Fin(F.Seq(n, F.Plus, F.D(1))),
            F.Comma, F.RowBreak, F.Grp(),
            Call("restrictedContextReadout", context, subset, matrix, ell, j),
            F.Sp, F.Eq, F.Sp,
            Call("trace", Call("mul", matrix, Projector(context, ell, j))), F.Dot));
    }

    private static Formula Overlap(Formula n, Formula context)
    {
        Formula ell = F.Id("ell");
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula r = F.Id("r");
        return F.Seq(
            F.Forall, F.Sp, ell, F.Comma, F.Sp, k, F.Comma, F.Sp, j, F.Comma, F.Sp, r,
            F.Comma, F.Sp,
            Call("trace", Call("mul", Projector(context, ell, j),
                Projector(context, k, r))), F.Sp, F.Eq, F.Sp,
            Call("if", Call("Eq", ell, k),
                Call("if", Call("Eq", j, r), F.D(1), F.D(0)),
                Call("inverse", Seq(n, F.Plus, F.D(1)))));
    }

    private static Formula CommonPremises(Formula n, Formula context) => F.Seq(
        n, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Sp,
        F.D(1), F.Sp, F.Leq, F.Sp, n, F.Comma, F.Sp,
        context, F.Colon, F.Sp, ContextType(n), F.Comma, F.RowBreak, F.Grp(),
        Overlap(n, context));

    private static Formula WitnessFormula()
    {
        Formula n = F.Id("n");
        Formula context = F.Id("C");
        Formula subset = F.Id("S");
        Formula ell = F.Id("ell");
        Formula p0 = Projector(context, ell, F.D(0));
        Formula p1 = Projector(context, ell, F.D(1));
        return F.Disp(F.Seq(
            F.Forall, F.Sp, CommonPremises(n, context), F.Comma, F.Sp,
            subset, F.Colon, F.Sp, Call("Finset", Fin(F.Seq(n, F.Plus, F.D(2)))), F.Comma,
            F.Sp, ell, F.InMacro, F.Sp, Fin(F.Seq(n, F.Plus, F.D(2))), F.Comma, F.Sp,
            ell, F.Sp, F.Neg, F.Sp, F.InMacro, F.Sp, subset,
            F.Sp, F.Rightarrow, F.RowBreak, F.Grp(),
            p0, F.Sp, F.Neq, F.Sp, p1, F.Sp, F.Land, F.Sp,
            Call("restrictedContextReadout", context, subset, p0), F.Sp, F.Eq, F.Sp,
            Call("restrictedContextReadout", context, subset, p1), F.Dot));
    }

    private static Formula ClassificationFormula()
    {
        Formula n = F.Id("n");
        Formula context = F.Id("C");
        Formula subset = F.Id("S");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, CommonPremises(n, context), F.Comma, F.Sp,
            subset, F.Colon, F.Sp, Call("Finset", Fin(F.Seq(n, F.Plus, F.D(2)))), F.Comma,
            F.RowBreak, F.Grp(),
            Call("Injective", Call("restrictedContextReadout", context, subset)),
            F.Sp, F.Iff, F.Sp, subset, F.Sp, F.Eq, F.Sp, Call("univ"), F.Dot));
    }
}
