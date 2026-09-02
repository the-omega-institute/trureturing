using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Algebra;

internal sealed class DualityInsufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Algebra/DualityInsufficiency."
            + "duality_insufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal split duality does not force zero drift or a positive invariant metric.",
        H("Duality Insufficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("duality-insufficiency"),
            DeclarationHandle.Create(Declaration),
            H("Split duality does not select the unitary boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two diagonal multipliers are constructed from arbitrary real "
                        + "drift and phase parameters and an arbitrary strictly positive "
                        + "observation period. The branch exchange is the canonical qubitX "
                        + "matrix already owned by the finite-dimensional matrix family.")),
                Paragraph(Text(
                    "Reflection, determinant one, reciprocal branch exchange, nonunit "
                        + "multipliers, and preservation of the split bilinear form all hold "
                        + "at nonzero drift. The imported positive-metric selection theorem "
                        + "then rules out every positive definite invariant Hermitian metric."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula delta = DeltaLower;
        Formula gamma = GammaLower;
        Formula period = F.Id("P");
        Formula exponent = F.Id("a");
        Formula forward = F.Id("u");
        Formula backward = F.Id("v");
        Formula monodromy = F.Id("M");
        Formula rho = Rho;
        Formula duality = F.Id("D");
        Formula metric = F.Id("H");
        Formula swap = F.Id("qubitX");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula matrix = Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), complex);

        Formula exponentValue = Seq(
            Open, delta, Sp, Plus, Sp, F.Id("i"), gamma, Close,
            Sp, Cdot, Sp, period);
        Formula forwardValue = Call("exp", exponent);
        Formula backwardValue = Call("exp", Seq(Minus, exponent));
        Formula modeVector = Grp(
            OpenBracket, forward, Comma, Sp, backward, CloseBracket);
        Formula rhoValue = Seq(
            Frac, Grp(D(1)), Grp(D(2)), Sp, Plus, Sp,
            delta, Sp, Plus, Sp, F.Id("i"), gamma);

        Formula reflection = Seq(
            Call("xiReading", Seq(D(1), Sp, Minus, Sp, rho)),
            Sp, Eq, Sp, Call("xiReading", rho));
        Formula determinantOne = Seq(Call("det", monodromy), Sp, Eq, Sp, D(1));
        Formula inverse = Seq(monodromy, Caret, Grp(Minus, D(1)));
        Formula branchExchange = Seq(
            swap, Sp, Cdot, Sp, monodromy, Sp, Cdot, Sp, swap,
            Sp, Eq, Sp, inverse);
        Formula reciprocal = Seq(
            forward, Sp, Cdot, Sp, backward, Sp, Eq, Sp, D(1));
        Formula nonunitForward = Seq(new Formula.Norm(forward), Sp, Neq, Sp, D(1));
        Formula nonunitBackward = Seq(new Formula.Norm(backward), Sp, Neq, Sp, D(1));
        Formula transpose = Seq(monodromy, Caret, Grp(F.Id("T")));
        Formula splitInvariant = Seq(
            transpose, Sp, Cdot, Sp, swap, Sp, Cdot, Sp, monodromy,
            Sp, Eq, Sp, swap);
        Formula dualityValue = Grp(
            reflection, Sp, Land, RowBreak, Grp(),
            determinantOne, Sp, Land, RowBreak, Grp(),
            branchExchange, Sp, Land, RowBreak, Grp(),
            reciprocal, Sp, Land, RowBreak, Grp(),
            nonunitForward, Sp, Land, Sp, nonunitBackward, Sp, Land, RowBreak, Grp(),
            splitInvariant);

        Formula exponentDefinition = Let(exponent, complex, exponentValue);
        Formula forwardDefinition = Let(forward, complex, forwardValue);
        Formula backwardDefinition = Let(backward, complex, backwardValue);
        Formula matrixDefinition = Let(monodromy, matrix, Call("diagonal", modeVector));
        Formula rhoDefinition = Let(rho, complex, rhoValue);
        Formula dualityDefinition = Let(duality, proposition, dualityValue);
        Formula dualityDoesNotForceZero = Seq(
            Neg, Sp, Grp(duality, Sp, Rightarrow, Sp,
                delta, Sp, Eq, Sp, D(0)));
        Formula invariantMetric = Seq(
            Exists, Sp, Typed(metric, matrix), Comma, Sp,
            Call("PosDef", metric), Sp, Land, Sp,
            monodromy, Caret, Grp(Star), Sp, Cdot, Sp,
            metric, Sp, Cdot, Sp, monodromy, Sp, Eq, Sp, metric);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, delta, Comma, Sp, gamma, Comma, Sp,
            period, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow,
            RowBreak, Grp(),
            exponentDefinition, forwardDefinition, backwardDefinition,
            RowBreak, Grp(),
            matrixDefinition, rhoDefinition,
            RowBreak, Grp(),
            dualityDefinition,
            RowBreak, Grp(),
            duality, Sp, Land, Sp, dualityDoesNotForceZero, Sp, Land, Sp,
            Neg, Sp, invariantMetric, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Let(Formula value, Formula type, Formula definition) => Seq(
        Operatorname, Grp(F.Id("let")), Sp,
        Typed(value, type), Sp, Eq, Sp, definition, Semi, Sp);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
