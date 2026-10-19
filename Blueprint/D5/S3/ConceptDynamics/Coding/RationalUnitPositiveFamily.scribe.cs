using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class RationalUnitPositiveFamilyDocument : IScribeDocumentDefinition
{
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Pow(Formula a, byte k) => Call("power", a, D(k));
    private static Formula Scale(Formula a, Formula b) => Call("smul", a, b);
    private static Formula At(string f, Formula t) => Call(f, t);

    public DocumentDefinition Create()
    {
        Formula t = F.Id("t"), r = F.Id("r"), j = F.Id("j");
        Formula c = F.Id("c"), k = F.Id("K"), w = F.Id("W");
        Formula n = F.Id("n"), q = F.Id("q"), u = F.Id("u");
        Formula nt = At("N", t), pt = At("P", t);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Arbitrary given rational augmentation-ideal matrix units admit one strictly positive integral family with exact positive uniformizing depths and exact rectangular exchange distances.",
            H("A positive family from given rational matrix units"), Blocks(
                Describe.Lean(DescribeId.Create("given-rational-unit-positive-family"),
                    DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.theorem26_2"),
                    H("Synchronized positive factors in the given realization"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Let H be a finite nontrivial group of order q, and let n and d be positive integers. In the original n by n rational group-matrix ring, suppose that the given units e(a,b) satisfy e(a,b)e(c,f)=delta(b,c)e(a,f), every entry has augmentation zero, and e(1,1) is nonzero. No relation d<=n, involution condition, or ambient-identity condition on the diagonal sum is assumed. The Lean indices start at zero; zero extension serves only to write finite sums in these same matrices.")),
                        Paragraph(Text("For 1<=t<=d, set N(t)=sum over 1<=a<t of e(a,a+1) and P(t)=sum over 1<=a<t of e(a,a). Choose one positive integer c clearing every coefficient of every given unit. Choose one positive integer K strictly exceeding the absolute values of all coefficients of cN(t) and cP(t), simultaneously for the whole family. Let u be the sum of all group elements and let J be the n by n matrix with every entry one.")),
                        Paragraph(Math(Disp(Equal(w, Scale(k, Mul(F.Id("J"), u)))))),
                        Paragraph(Math(Disp(Equal(At("R", t), Add(w, Scale(c, pt)))))),
                        Paragraph(Math(Disp(Equal(At("S", t), Add(w, Scale(c, nt)))))),
                        Paragraph(Math(Disp(Equal(At("B", t), Add(Pow(w, 2), Scale(Pow(c, 2), nt)))))),
                        Paragraph(Text("All the displayed R(t), S(t) and B(t) have strictly positive integer group coefficients. The formulas are identities after the injective natural-to-rational coefficient map; hence the factors and endpoints are actual matrices over the natural group ring in the given realization.")),
                        Paragraph(Text("The unit relations give P(t)N(t)=N(t) and N(t)P(t)=N(t-1). Augmentation zero kills both cross terms with W. Consequently, for 2<=t<=d, the same two positive factors satisfy the two adjacent product identities.")),
                        Paragraph(Math(Disp(Equal(Mul(At("R", t), At("S", t)), At("B", t))))),
                        Paragraph(Math(Disp(Equal(Mul(At("S", t), At("R", t)), At("B", new Formula.Binary(t, FormulaBinaryOperator.Subtract, D(1))))))),
                        Paragraph(Math(Disp(Equal(Pow(w, 2), Scale(Mul(Mul(q, n), Pow(k, 2)), Mul(F.Id("J"), u)))))),
                        Paragraph(Math(Disp(Equal(Call("augmentation", At("B", t)), Scale(Mul(Mul(Pow(q, 2), n), Pow(k, 2)), F.Id("J")))))),
                        Paragraph(Text("For 1<=j<t, induction in the original matrix ring gives N(t)^j=sum over 1<=a<=t-j of e(a,a+j). The t-th power is zero. Multiplying the j-th power on the left by e(1,1) selects e(1,j+1), which is nonzero because its product with e(j+1,1) is e(1,1). This proves exact depth t without imposing that the sum of the units is the ambient identity. For t=1, N(1)=0 has least positive depth one; no claim about its zeroth power is needed.")),
                        Paragraph(Text("Quotient the rational group algebra by its ideal of uniform elements. The quotient kills W and preserves every nonzero positive power of the augmentation-zero shift, since augmentation together with this quotient is injective. The nonzero scalar c squared preserves the exact depth. Uniformity of a natural group matrix is equivalent to vanishing in this quotient, so its least positive uniformizing exponent is exactly t.")),
                        Paragraph(Math(Disp(Equal(Call("tau", At("B", t)), t)))),
                        Paragraph(Text("The adjacent factors construct chains in either direction, including an empty chain for t=r. For every competing rectangular exchange chain, map every vertex and factor through the same quotient and apply the general rectangular nilpotence-depth barrier. It bounds the two endpoint depths in both directions, so its length is at least the absolute depth difference. Intermediate dimensions are unrestricted, including zero wherever the chain interface permits it. The cases n=1, d=1 and either endpoint t=1 remain in scope.")),
                        Paragraph(Math(Disp(Equal(Call("minimumExchangeLength", At("B", t), At("B", r)), Call("dist", t, r))))),
                        Paragraph(Text("This construction chooses a new common positive baseline for the supplied units. It does not embed an arbitrary previously fixed inert matrix into the family."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("positive-family-supplied-constants"),
                    DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.positiveFamily_with_constants"),
                    H("The construction preserves supplied constants"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For the given rational augmentation-ideal matrix units, supply positive integers c,K and integer group matrices Z(a,b) whose rational casts equal c times e(a,b). Assume the absolute integer coefficients of both truncated sums from Z are strictly below K for every t<=d. The construction produces F with F.c=c and F.K=K, retaining every clause of PositiveFamily: exact factors, positivity, augmentation, positive tau, and rectangular exchange minima.")), Paragraph(Text("This is the original construction with its clearing and positivity inputs exposed at its original owner. The existing theorem26_2 prepares those inputs by its original common-denominator and finite-maximum arguments and consumes this result. The supplied constants are never replaced by newly chosen ones. A specialization to c=K=card(H) still requires the actual clearing and bound proofs; existence alone does not identify them."))),
                    DescribeRole.Theorem))));
    }
}
