using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class RadicalMultiplicityDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sum of polynomial multiples of quadratic radicals is determined by a quadratic initial jet.",
        H("Local multiplicity of polynomial radical sums"),
        Blocks(Describe.Lean(
            DescribeId.Create("cdso-radical-sum-cutoff"),
            DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/RadicalMultiplicity.sum_eq_zero_of_coeff_eq_zero"),
            H("A cutoff allowing repeated radicals and cancellation"),
            StatementSource.FromAuthor(Disp(All("I", Call("Type"), Seq(
                OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
                All("S", new Formula.TypeArrow(F.Id("I"), Call("RealPowerSeries")),
                All("p", new Formula.TypeArrow(F.Id("I"), Call("RealPolynomial")),
                All("A", new Formula.TypeArrow(F.Id("I"), Call("RealPolynomial")), Seq(
                    Call("RadicalData", F.Id("I"), F.Id("S"), F.Id("p"), F.Id("A")), Sp, Land, Sp,
                    Open, All("k", F.Id("Nat"), Seq(F.Id("k"), Sp, Le, Sp,
                        D(3), Call("card", F.Id("I")), Caret, Grp(D(2)), Sp, Implies, Sp,
                        Call("coeff", F.Id("k"), Call("RadicalSum", F.Id("S"), F.Id("A"))),
                        Sp, Eq, Sp, D(0))), Close, Sp, Implies, Sp,
                    Call("RadicalSum", F.Id("S"), F.Id("A")), Sp, Eq, Sp, D(0))))))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let I be any finite type, n its cardinality, p_i and A_i real polynomials, and S_i real formal power series. RadicalData means S_i squared equals p_i, the constant coefficient of S_i is nonzero, the degree of p_i is at most two, and the degree of A_i is at most n, for every i. Put Z equal to the sum of A_i S_i. If every coefficient of Z from zero through 3n squared, inclusive, is zero, then Z is the zero series. Zero polynomials, constant radicands, repeated S_i, arbitrary signs and the empty index type are allowed.")),
                Paragraph(Text("Select an independent subfamily of the summands over the real constants. Embed its series into the Laurent-series differential field; its derivative has exactly the real constants as kernel. The differential-field Wronskian criterion makes the selected Wronskian nonzero. Iterated differentiation of A times S, with S squared equal to p, gives S p to the negative v times B_v, where B_0=A and B_(v+1)=p B_v' +(1/2-v)p'B_v. The bound degree B_v<=d+2v gives Wronskian order at most l(d+2(l-1)) for a selected family of size l with coefficient degrees at most d. A nonzero constant linear combination therefore has order at most l(d+2(l-1))+l-1. With d=n and l<=n this is below 3n squared. Replacing a column by Z transfers a long initial zero jet to that determinant and contradicts its degree bound. The independent span may have dimension one, and the original summands need not be independent.")),
                Paragraph(Text("This theorem concerns formal series over the reals. Its application to actual allocation functions requires the analytic extension, coefficient correspondence and source term-count calculation in CdsoAllocationGerms. It makes no assertion about distinct real zeros or global behavior."))),
            DescribeRole.Theorem))));
}
