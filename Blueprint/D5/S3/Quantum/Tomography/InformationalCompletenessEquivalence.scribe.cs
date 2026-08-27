using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class InformationalCompletenessEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centered quantum readout completeness has four equivalent real-linear forms.",
        H("Informational Completeness Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quantum-informational-completeness-has-four-equivalent-forms"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence."
                        + "informational_completeness_four_way"),
                H("Quantum informational completeness has four equivalent forms"),
                StatementSource.FromAuthor(CompletenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each E_i is a real traceless Hermitian effect direction. Its span is "
                            + "the centered visible space. The full visible space is constructed "
                            + "as the scalar identity line plus the embedded centered span, and "
                            + "the invisible residual is its Hilbert-Schmidt orthogonal complement.")),
                    Paragraph(Text(
                        "The observer signature records the real trace expectation of every "
                            + "centered effect on each positive trace-one density state. Explicit "
                            + "perturbations about the maximally mixed state identify its "
                            + "injectivity with full centered span; finite-dimensional orthogonal "
                            + "decomposition identifies zero residual with full visibility."))),
                DescribeRole.Theorem))));

    private static Formula CompletenessFormula()
    {
        Formula d = F.Id("d"), indexType = F.Id("A"), effects = F.Id("E");
        Formula index = F.Id("i"), rho = Rho;
        Formula hermitian = Seq(
            Operatorname, Grp(F.Id("Herm")), Underscore, Grp(d));
        Formula traceZero = Seq(hermitian, Caret, Grp(D(0)));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula centeredVisible = new Formula.Subscript(F.Id("V"), D(0));
        Formula visible = F.Id("V"), residual = F.Id("N");
        Formula effect = new Formula.Subscript(effects, index);
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula signature = Seq(
            Open, rho, Colon, Sp, stateType, Sp, Mapsto, Sp,
            Open, index, Colon, Sp, indexType, Sp, Mapsto, Sp,
            Re, Sp, Call("Tr", Seq(Call("matrix", rho), Sp, effect)), Close,
            Close);

        Formula definitions = Seq(
            centeredVisible, Sp, Eq, Sp,
            Call("span", Seq(reals, Comma, Sp,
                Open, effect, Colon, Sp, index, InMacro, Sp, indexType, Close)),
            Comma, Sp,
            visible, Sp, Eq, Sp, reals, F.Id("I"), Sp, Plus, Sp, centeredVisible,
            Comma, RowBreak,
            Grp(), residual, Sp, Eq, Sp,
            visible, Caret, Grp(Perp));

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, Sp, indexType, Colon, Sp,
            Seq(Operatorname, Grp(F.Id("Type"))), Comma, RowBreak,
            Grp(), effects, Colon, Sp, indexType, Sp, To, Sp, traceZero, Comma, RowBreak,
            Grp(), definitions, Comma, RowBreak,
            Grp(), Call("Injective", signature), Sp, Iff, Sp,
            residual, Sp, Eq, Sp, OpenBrace, D(0), CloseBrace, Sp, Iff, Sp,
            visible, Sp, Eq, Sp, hermitian, Sp, Iff, RowBreak,
            Grp(), centeredVisible, Sp, Eq, Sp, traceZero, Dot));
    }
}
