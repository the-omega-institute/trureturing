using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RealRootedPermutations;

internal sealed class RealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer exponent heights realize every unimodal coefficient ordering strictly.",
        H("Realizing Unimodal Coefficient Permutations"),
        Blocks(
            Describe.Lean(DescribeId.Create("realization-product-zpow"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Realization.product_zpow"),
                H("A product of integer powers"),
                StatementSource.FromAuthor(Disp(ProductZpow())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonzero real base, multiplying integer powers over a finite set adds their exponents. This identity combines the individual site factors in the reciprocal-weight calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unimodal-positive-product-strict-realization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Realization.realize_strict"),
                H("Every unimodal permutation has a strict realization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural n and every unimodal permutation of Fin(n+1), there are n+1 strictly positive real numbers r(i) such that the nonconstant coefficients of the product of 1+r(i)x strictly increase in the specified permutation order. Permutation value v denotes coefficient index v+1; the constant coefficient is omitted.")),
                    Paragraph(Text("Write N=n+1 and let rho be the inverse permutation. Assign A(v)=2^(n-rho(v)), H(0)=0 and H(v+1)=2^N-A(v). The integer increments b(i)=H(i+1)-H(i) strictly decrease: before the peak, the preceding weight is at least twice the current weight; after the peak, the following weight is at least twice the current weight. The first increment is treated using A(0) at most 2^n.")),
                    Paragraph(Text("Choose T=2^N+1 and r(i)=T^b(i), with integer powers. Finset.prod_one_add expands the polynomial, and coefficient extraction retains exactly the subsets of cardinality k. Since b is decreasing, the first k indices maximize the exponent sum. To compare any subset with this initial segment, Finset.orderEmbOfFin lists its elements increasingly; its j-th element is at least j. Summing the increments on the initial segment telescopes to H(k).")),
                    Paragraph(Text("Each subset product is positive and at most T^H(k), while the initial segment contributes exactly T^H(k). There are at most 2^N subsets, so T^H(k) is at most the k-th coefficient and that coefficient is at most 2^N times T^H(k). Increasing inverse positions increase the integer heights by at least one. Since 2^N is strictly less than T, the upper bound at one height is strictly below the lower bound at the next height. These inequalities prove the required strict sorting, including the one-factor case."))),
                DescribeRole.Theorem))));

    private static Formula ProductZpow()
    {
        Formula iota = F.Id("I"), s = F.Id("S"), b = F.Id("b"), t = F.Id("T"), i = F.Id("i");
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula finset = new Formula.FunctionCall(FormulaIdentifier.Create("Finset"), [iota]);
        Formula exponent = new Formula.Apply(b, [i]);
        Formula equation = Equal(
            Seq(new Formula.Subscript(Prod, Seq(i, InMacro, Sp, s)), Sp,
                new Formula.Power(t, exponent)),
            new Formula.Power(t,
                Seq(new Formula.Subscript(Sum, Seq(i, InMacro, Sp, s)), Sp, exponent)));
        Formula nonzero = new Formula.Relation(t, FormulaRelationOperator.NotEqual, D(0));
        Formula body = new Formula.Logic(nonzero, FormulaLogicOperator.Implies, equation);
        body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("T"), real, body);
        body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("b"),
            new Formula.TypeArrow(iota, integer), body);
        body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("S"), finset, body);
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("I"),
            Seq(Operatorname, Grp(F.Id("Type"))), body);
    }
}
