using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Fredholm;

internal sealed class PositiveFredholmProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted reciprocal-square summability makes the positive square-folded spectral "
            + "product converge and increase on the nonnegative axis.",
        H("Positive Fredholm Product Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-fredholm-product-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Fredholm/PositiveFredholmProduct."
                        + "positive_fredholm_completion"),
                H("The positive square-folded spectral product converges monotonically"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive ordinates gamma and their natural-number multiplicities "
                            + "are abstract inputs. The only analytic input is summability of "
                            + "the multiplicity-weighted reciprocal squares. Expanding each "
                            + "multiplicity as a finite fiber turns this into summability of the "
                            + "individual nonnegative increments.")),
                    Paragraph(Text(
                        "Pinned Mathlib's logarithmic infinite-product criterion proves "
                            + "multipliability for every nonnegative x. The exponential formula "
                            + "for the product then gives the lower bound one and carries "
                            + "termwise monotonicity to the completed product. At x = 0 every "
                            + "factor is one, so the product is normalized.")),
                    Paragraph(Text(
                        "The accompanying Lean module also supplies a nonempty Basel witness "
                            + "with gamma_i = i + 1 and unit multiplicity, including convergence "
                            + "at x = 1, and proves that multiplicity m_i = i makes the required "
                            + "weighted series diverge.")),
                    Paragraph(Text(
                        "The Riemann-hypothesis description of the ordinates and the zero-density "
                            + "theorem producing the summability premise remain external inputs. "
                            + "No countable trace-class operator or Fredholm determinant is "
                            + "claimed, because the pinned library does not provide the required "
                            + "operator API."))),
                DescribeRole.Theorem))));

    private static Formula CompletionFormula()
    {
        Formula indexType = F.Id("iota");
        Formula index = F.Id("i");
        Formula gamma = F.Id("gamma");
        Formula multiplicity = F.Id("m");
        Formula x = F.Id("x");
        Formula product = F.Id("F");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula gammaAt = Apply(gamma, index);
        Formula multiplicityAt = Apply(multiplicity, index);
        Formula square = Seq(Grp(gammaAt), Caret, D(2));
        Formula weight = Seq(multiplicityAt, Sp, Slash, Sp, square);
        Formula factor = Seq(
            Grp(D(1), Sp, Plus, Sp, x, Sp, Slash, Sp, square),
            Caret, Grp(multiplicityAt));
        Formula productAt = Apply(product, x);
        Formula nonnegative = Seq(D(0), Sp, Leq, Sp, x);

        Formula hypotheses = Seq(
            Grp(Forall, Sp, index, InMacro, Sp, indexType, Comma, Sp,
                D(0), Sp, Lt, Sp, gammaAt),
            Sp, Land, Sp,
            Call("Summable", Lambda(index, weight)));
        Formula conclusions = Seq(
            Grp(Forall, Sp, x, InMacro, Sp, reals, Comma, Sp,
                nonnegative, Sp, Rightarrow, Sp,
                Call("Multipliable", Lambda(index, factor))),
            Sp, Land, Sp,
            Apply(product, D(0)), Sp, Eq, Sp, D(1),
            Sp, Land, Sp,
            Grp(Forall, Sp, x, InMacro, Sp, reals, Comma, Sp,
                nonnegative, Sp, Rightarrow, Sp,
                D(1), Sp, Leq, Sp, productAt),
            Sp, Land, Sp,
            Call("MonotoneOn", product, Call("Ici", D(0))));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Colon, Sp, F.Id("Type"), Comma, Sp,
                gamma, Colon, Sp, indexType, Sp, To, Sp, reals, Comma, Sp,
                multiplicity, Colon, Sp, indexType, Sp, To, Sp, naturals, Comma),
            Seq(
                productAt, Sp, Eq, Sp,
                Prod, Underscore, Grp(index, InMacro, Sp, indexType), Sp, factor, Comma),
            Seq(hypotheses, Sp, Rightarrow, Sp, conclusions, Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(LambdaLower, Sp, variable, Sp, Mapsto, Sp, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
