using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class DyadicRootFiberArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd part q of a positive degree determines its cyclic multiplication kernel and the exact cardinality q of every root fiber in the dyadic solenoid.",
        H("Exact Root Arithmetic in the Dyadic Solenoid"),
        Blocks(
            Paragraph(Text(
                "Use the existing DyadicSolenoid from DyadicTimeSeparation: sequences in AddCircle(1) satisfying 2 x(n+1)=x(n), "
                + "with the topology inherited from the product of circles. Circle period one is fixed throughout. "
                + "No new carrier or replacement topology is introduced.")),
            Describe.Lean(
                DescribeId.Create("dyadic-root-fiber-arithmetic"),
                DeclarationHandle.Create("D5/S1/Solenoid/DyadicRootFiberArithmetic.dyadic_root_fiber_arithmetic"),
                H("Cyclic kernels and exact root fibers"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural k and odd natural q, put m=2^k q. The kernel of the additive multiplication homomorphism by m "
                        + "is additively equivalent to ZMod q. For every a in S2 the subtype of x satisfying m x=a is finite and its Nat.card is q. "
                        + "Oddness implies q is positive; q=1, k=0 and m=1 are included. Every positive natural degree has this factorization "
                        + "by Nat.exists_eq_two_pow_mul_odd. Thus multiplication by powers of two is bijective, and all other positive degrees "
                        + "have exactly their odd part many roots at each target.")),
                    Paragraph(Text(
                        "Write q=2d+1 and s=d+1. On q-torsion in the circle, 2s acts as q+1, hence as the identity. "
                        + "Compatibility therefore forces x(n+1)=s x(n), so x(n)=s^n x(0). Conversely each ZMod q element z gives "
                        + "the compatible sequence s^n ZMod.toAddCircle(z). Coordinate zero proves injectivity using ZMod.toAddCircle_injective. "
                        + "AddCircle.nsmul_eq_zero_iff supplies every possible initial coordinate as r/q modulo one, proving surjectivity. "
                        + "The zero kernel of doubling in dyadic_time_separation removes the factor 2^k. Its positive-degree surjectivity, "
                        + "together with AddMonoidHom.fiberEquivKerOfSurjective, identifies each root fiber with that cyclic kernel.")),
                    Paragraph(Text(
                        "For the doubling dynamics T(x)=2x, induction gives T iterated n times equal to multiplication by 2^n. "
                        + "For n>0, T^n(x)=x is equivalent to (2^n-1)x=0; the latter degree is odd. "
                        + "Consequently the number of points fixed by the n-th iterate is exactly 2^n-1. "
                        + "This counts points whose period divides n, not points of least period exactly n. "
                        + "It is a consequence of the root arithmetic, without an entropy assertion.")),
                    Paragraph(Text(
                        "There is also an alternative algebraic rational-time construction. Apply "
                        + "FiniteRootFiberCoherence.finite_root_fibers_rational_coherence with H=Multiplicative S2 and h=Multiplicative.ofAdd thirdPoint. "
                        + "The exact arithmetic above gives finite root fibers in every positive degree, and dyadic_time_separation supplies their nonemptiness. "
                        + "The finite inverse-system theorem then gives a homomorphism from Multiplicative Q to Multiplicative S2 carrying 1 to h, "
                        + "equivalently an additive rational homomorphism with value thirdPoint at 1. This is an alternative inference to the parent's Baer argument, "
                        + "not a new existence assertion. The parent also proves every such rational homomorphism is discontinuous in the usual rational topology "
                        + "and that no continuous real homomorphism reaches thirdPoint at time 1. Algebraic coherence therefore supplies no continuous time flow there.")),
                    Paragraph(Text(
                        "These are classical solenoid arithmetic and dynamics phenomena. R. N. Gumerov, On finite-sheeted covering mappings onto solenoids, "
                        + "arXiv:math/0312288v1, gives context for power maps on solenoids. The proof here uses the specified additive inverse-limit carrier directly. "
                        + "No literature novelty or formal identification with another solenoid model is claimed."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);

    private static Formula Statement()
    {
        var m = new Formula.Binary(new Formula.Power(D(2), V("k")), FormulaBinaryOperator.Multiply, V("q"));
        var fiber = Call("RootFiber", m, V("a"));
        var arithmetic = Both(Call("Nonempty", Call("AddEquiv", Call("Kernel", Call("nsmul", m, V("S2"))), Call("ZMod", V("q")))),
            All("a", V("S2"), Both(Call("Finite", fiber),
                new Formula.Relation(Call("Nat.card", fiber), FormulaRelationOperator.Equal, V("q")))));
        return Disp(All("k", V("N"), All("q", V("N"),
            new Formula.Logic(Call("Odd", V("q")), FormulaLogicOperator.Implies, arithmetic))));
    }
}
