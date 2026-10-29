using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class ArchimedeanTimeRigidityDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [..v], f);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula And(Formula a, Formula b) =>
        Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Statement => All(
        Imp(And(Seq(D(1), Sp, F.Lt, Sp, I("p")),
                And(All(Imp(Equal(Call("nsmul", I("p"), I("x")), D(0)),
                            Equal(I("x"), D(0))), B("x", I("A"))),
                    Call("Continuous", I("f")))),
            Seq(Call("Injective", I("f")), Sp, Lor, Sp, Equal(I("f"), D(0)))),
        B("K", I("ArchimedeanOrderedFieldWithOrderTopology")),
        B("A", I("TOneAddGroup")), B("p", I("Nat")),
        B("f", Call("AddHom", I("K"), I("A"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero continuous homomorphism from Archimedean field time into a group without p-torsion is injective.",
        H("Archimedean time rigidity"), Blocks(
        Paragraph(Text("Let K be an Archimedean linearly ordered field equipped with its order topology. Let A be an arbitrary additive group with a T1 topology, in a universe independent of K. In the formula, ArchimedeanOrderedFieldWithOrderTopology and TOneAddGroup abbreviate exactly these assumptions. The group A may be noncommutative, and continuity of its group operations is not assumed.")),
        Describe.Lean(DescribeId.Create("continuous-addhom-injective-or-eq-zero"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity.continuous_addHom_injective_or_eq_zero"),
            H("Injectivity or triviality"), StatementSource.FromAuthor(Disp(Statement)),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Fix a natural number p greater than one. Assume that p*x=0 implies x=0 for every x in A, where p*x denotes repeated addition. Every continuous additive homomorphism f:K->A is injective or is the zero homomorphism. The condition concerns only the fiber over zero; it does not assume injectivity of the entire p-fold multiplication map. No primality or absence of torsion at other integers is required."))), DescribeRole.Theorem),
        Paragraph(Text("Put S=ker(f). If S is the zero subgroup, f is injective. Otherwise, suppose a were its least positive element. The element b=a/p satisfies 0<b<a and p*b=a. Additivity gives p*f(b)=f(a)=0, so the target hypothesis gives f(b)=0. Thus b also belongs to S, contradicting leastness. The Archimedean subgroup density theorem now makes S dense. The set S is closed because it is the inverse image of the closed singleton {0} under the continuous map f. A closed dense subgroup is the whole field, hence f=0.")),
        Paragraph(Text("Both the rational field with its usual topology and the real field satisfy the source assumptions. Consequently a nontrivial continuous time homomorphism from either field into such a target cannot have a nonzero period: f(t)=0 forces t=0. A period in the sense f(s+t)=f(s) gives f(t)=0 by additivity and cancellation. This is injectivity, with no assertion that the map is a topological embedding or that its image is closed.")),
        Paragraph(Text("For a multiplicative group H, use A=Additive(H) with its supplied topology. The target assumption becomes x^p=1 implies x=1, and the zero homomorphism becomes the constant identity homomorphism. This is a change of notation and does not impose commutativity or a global unique-root property. The argument combines standard subgroup density and closedness results with the division-closed kernel observation; no literature priority or physical realization claim is made."))
        )));
}
