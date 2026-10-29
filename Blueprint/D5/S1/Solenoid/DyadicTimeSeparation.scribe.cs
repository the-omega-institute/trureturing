using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class DyadicTimeSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compact connected dyadic solenoid admits algebraic rational time at a nonzero order-three point, but no continuous rational or real time there.",
        H("Algebraic and Continuous Time in the Dyadic Solenoid"),
        Blocks(
            Paragraph(Text(
                "Let S2 be the additive subgroup of the product of unit additive circles consisting of sequences x with 2 times x(n+1) equal to x(n). "
                + "Its topology is the subspace topology of that product. This is the dyadic carrier, distinct from the all-positive-degree UniversalSolenoid: "
                + "only doubling compatibility is imposed here, and S2 has a nonzero point h with coordinates (-1)^n/3 modulo one.")),
            Describe.Lean(
                DescribeId.Create("dyadic-solenoid-time-separation"),
                DeclarationHandle.Create("D5/S1/Solenoid/DyadicTimeSeparation.dyadic_time_separation"),
                H("A divisible compact connected group separates algebraic and continuous time"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "S2 is a compact connected abelian topological group. For every positive integer m, multiplication by m is surjective. "
                        + "Multiplication by two has zero kernel. The point h is nonzero and 3 times h is zero. "
                        + "There exists an additive homomorphism phi from the rational numbers to S2 with phi(1)=h. "
                        + "Every such homomorphism satisfies phi((1/4)^n)=h for every natural n and is discontinuous for the usual rational topology. "
                        + "There is no continuous additive homomorphism psi from the real numbers to S2 with psi(1)=h.")),
                    Paragraph(Text(
                        "The map j from the real line has coordinate j(t)(n)=t/2^n modulo one. It is a continuous additive homomorphism with dense image. "
                        + "For a finite set of coordinates choose its largest index N, lift x(N) to a real representative r, and take t=2^N r. "
                        + "Compatibility matches every earlier coordinate exactly. The compatibility equations are closed equalizers in a compact product, proving compactness; "
                        + "the dense continuous image of the connected real line proves connectedness. The image of multiplication by a positive m is compact and closed. "
                        + "It contains j of the real line because t/m is a real preimage, so density makes multiplication surjective.")),
                    Paragraph(Text(
                        "Compatibility also shows that a point killed by doubling has every coordinate zero. At the alternating third-period point, "
                        + "doubling negates each coordinate and tripling kills it. Divisibility makes the underlying abelian group injective as an integer module. "
                        + "Baer's extension property extends the homomorphism from the integers sending 1 to h along the inclusion of the integers into the rationals. "
                        + "This constructs a genuine additive rational homomorphism without imposing continuity.")),
                    Paragraph(Text(
                        "Doubling is injective, hence so is multiplication by four, and 4h=h. For any rational homomorphism anchored at h, "
                        + "the recurrence 4 phi((1/4)^(n+1))=phi((1/4)^n) therefore forces every value to equal h. "
                        + "The arguments tend to zero in the usual rational topology, while the image remains the nonzero constant h, contradicting continuity and Hausdorff uniqueness of limits. "
                        + "Restricting a continuous real homomorphism along the continuous rational inclusion gives the real-time obstruction. "
                        + "For the discrete topology on the rational domain every map is continuous; the obstruction concerns its usual topology. "
                        + "The dense real flow j exists, but cannot take the value h at time 1.")),
                    Paragraph(Text(
                        "These are classical solenoid phenomena. R. N. Gumerov, On finite-sheeted covering mappings onto solenoids, arXiv:math/0312288v1, "
                        + "defines the dyadic case by constant bonding degree two. Propositions 1 and 2 discuss surjective power maps and the homeomorphism property "
                        + "for primes repeated infinitely in the bonding sequence. That multiplicative-circle account provides classical context; "
                        + "the assertions here are proved directly on the displayed additive-circle carrier, without asserting a formally verified identification of the two models "
                        + "or a new result in the literature."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Both(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Conj(params Formula[] xs) =>
        xs.Length == 1 ? xs[0] : Both(xs[0], Conj(xs[1..]));
    private static Formula No(Formula x) => Seq(Neg, Open, x, Close);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);

    private static Formula Statement()
    {
        var s = V("S2");
        var h = V("h");
        var qhom = Call("AddHom", V("Q"), s);
        var rhom = Call("AddHom", V("R"), s);
        var quarter = new Formula.Fraction(D(1), D(4));
        return Disp(Conj(
            Call("Compact", s), Call("Connected", s),
            Call("Continuous", V("j")), Call("DenseRange", V("j")),
            All("m", V("N"), Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("m")),
                Call("Surjective", Call("multiplication", V("m"), s)))),
            All("x", s, Imp(Eqn(Mul(D(2), V("x")), D(0)), Eqn(V("x"), D(0)))),
            No(Eqn(h, D(0))), Eqn(Mul(D(3), h), D(0)),
            Ex("phi", qhom, Eqn(Call("phi", D(1)), h)),
            All("theta", qhom, Imp(Eqn(Call("theta", D(1)), h), Both(
                All("n", V("N"), Eqn(Call("theta", new Formula.Power(quarter, V("n"))), h)),
                No(Call("Continuous", V("theta")))))),
            No(Ex("psi", rhom, Both(Call("Continuous", V("psi")), Eqn(Call("psi", D(1)), h))))));
    }
}
