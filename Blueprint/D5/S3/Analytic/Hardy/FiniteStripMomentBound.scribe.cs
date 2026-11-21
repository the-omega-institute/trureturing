using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Hardy;

internal sealed class FiniteStripMomentBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Hardy/FiniteStripMomentBound.";
    private static readonly LibraryNoteRef SupportContext =
        LibraryNoteRef.Create("D5/L/Observer/lissy2026optimalfastheat");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-time strip bounds for Laplace moments", H("Finite-time strip bounds for Laplace moments"),
        Blocks(
            Describe.Lean(DescribeId.Create("entire-interpolation-with-one-sided-growth"),
                DeclarationHandle.Create(Owner + "entire_strip_bound"),
                H("Finite product bound for entire interpolation"), StatementSource.FromAuthor(Growth()),
                AssessedProvenance.FromRepo(SupportContext),
                Blocks(
                    Paragraph(Text("Write rᵢ = √(qᵢ²+β²). The input is an entire function whose norm at each z is at most M exp(L max(0, −Re z)), with M nonnegative. It takes value one at the selected node and vanishes at every other node in a finite family of distinct nonnegative real nodes indexed by a finite type I with decidable equality. The bound holds for every positive strip parameter β and every L ≥ 0.")),
                    Paragraph(Text("The Cayley map gives u in the right half-plane. At z = β(u − 1/u)/2, multiplication by exp(−Lβ/(2u)) cancels the possible growth where Re z is negative. The disk bound then applies with constant M. For nodes q and r the pseudohyperbolic distance is |q−r| divided by the sum of their radii, where the radius at q is √(q²+β²). At the selected node the damping has modulus exp(−L(√(q²+β²)−q)/2)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-window-moment-norm"),
                DeclarationHandle.Create(Owner + "windowNorm_lower_bound"),
                H("Lower bound for the exact Kronecker moments"), StatementSource.FromAuthor(Moment()),
                AssessedProvenance.FromRepo(SupportContext),
                Blocks(
                    Paragraph(Text("The time L and strip parameter β are positive, with rᵢ = √(qᵢ²+β²). Let q be any injective family of nonnegative real nodes indexed by a finite type I with decidable equality, and let j be an index. The moment conditions integrate h(s) exp(−qₖs) against Lebesgue measure on (0,L), with h real and square-integrable there. The moments equal one at the selected node and zero at the others. The resulting norm bound is the product of the reciprocal distances times the damping at the selected node, divided by √L.")),
                    Paragraph(Text("The finite-window Laplace transform is entire by differentiation under the integral. Its growth constant is at most √L times the L² norm of h by Cauchy–Schwarz. Distinctness makes every factor being inverted positive. Lissy's Proposition 2.1 gives the exact-support context for a continuum heat equation through two Hardy conditions. The finite-window inequality here uses the support directly in the integral and yields an explicit product for arbitrary finite nodes."))),
                DescribeRole.Theorem))));

    private static Formula L => F.Id("L");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula Q(Formula i) => Seq(F.Id("q"), Underscore, Grp(i));
    private static Formula R(Formula i) => Seq(F.Id("r"), Underscore, Grp(i));
    private static Formula Damping => new Formula.Apply(Exp,
        [new Formula.Fraction(Seq(Minus, L, Open, R(J), Minus, Q(J), Close), D(2))]);
    private static Formula Distance(bool reciprocal)
    {
        Formula numerator = new Formula.Absolute(Seq(Q(J), Minus, Q(K)));
        Formula denominator = Seq(R(J), Plus, R(K));
        return Seq(Prod, Underscore, Grp(K, InMacro, Sp, F.Id("I"), Setminus, OpenBrace, J, CloseBrace),
            Sp, reciprocal ? new Formula.Fraction(denominator, numerator)
                : new Formula.Fraction(numerator, denominator));
    }

    private static Formula Growth() => Disp(Seq(Damping, Sp, Le, Sp, F.Id("M"), Sp, Distance(false)));

    private static Formula Moment() => Disp(Seq(new Formula.Fraction(
        Seq(Distance(true), Sp, Damping), Seq(Sqrt, Grp(L))), Sp, Le, Sp,
        Seq(new Formula.Norm(F.Id("h")), Underscore,
            Grp(new Formula.Power(F.Id("L"), D(2)), Open, D(0), Comma, L, Close))));
}
