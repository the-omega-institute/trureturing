using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProjectionRange;

internal sealed class UniformTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invertible transport of continuous idempotents",
        H("Invertible transport of continuous idempotents"),
        Blocks(
            Paragraph(Text("TransportData in the formula consists of arbitrary types T and R, a topology on T, a PreconnectedSpace T instance, a NormedRing R instance, a CompleteSpace R instance, a map P:T -> R, a proof that P is continuous, and proofs P(t)P(t)=P(t) for every t:T. Parameter(q) is T, Ring(q) is R, Units(Ring(q)) is the group of two-sided units of R, and P(q,t) is the given idempotent. Thus the data quantifier retains every type, instance, map and hypothesis in the theorem. In the equation, a unit is coerced to its value in R, and multiplication has its original noncommutative order.")),
            Describe.Lean(
                DescribeId.Create("uniformtransport"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/UniformTransport.connected_idempotents_intertwiner"),
                H("connected_idempotents_intertwiner"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any two parameters s,t in a preconnected space, there is a unit u with P(t)u=uP(s). The conclusion is an existence statement for each pair; it does not select a continuously varying u as a function of the pair. The ring need not be commutative, and neither a path between s and t nor an initial invertible intertwiner is supplied.")),
                    Paragraph(Text("For idempotents p and q put w(p,q)=qp+(1-q)(1-p). At q=p, idempotence gives w(p,p)=p+(1-p)=1. Also q w(p,q)=qp=w(p,q)p, since q(1-q)=0 and (1-p)p=0. These identities use only the ring laws and the two idempotence equations; they do not interchange any factors.")),
                    Paragraph(Text("Fix a parameter a. The map b |-> w(P(a),P(b)) is continuous and equals 1 at b=a. In a complete normed ring the set of units is open, so throughout a neighborhood of a this shuffle is the value of a unit u. The shuffle identity gives P(b)u=uP(a). Multiplying this equation by u^(-1) on both sides gives P(a)u^(-1)=u^(-1)P(b). Consequently the relation a~b defined by existence of such a unit holds locally in both directions.")),
                    Paragraph(Text("The relation is transitive: if P(b)u=uP(a) and P(c)v=vP(b), then P(c)(vu)=(vu)P(a), and vu is a unit. Preconnected induction for a locally symmetric transitive relation now gives s~t for arbitrary s,t. This is the local-to-global step; path connectedness is unnecessary. If T is empty there are no s,t to instantiate, and the statement remains valid without a nonempty-space assumption.")),
                    Paragraph(Text("The proof uses the standard openness-of-units argument in normed rings and preconnected induction, provided here by Mathlib Units.isOpen and PreconnectedSpace.induction₂'. The shuffle is the classical algebraic device for comparing idempotents. This presentation makes no literature-priority claim. Applied in the complete normed ring of continuous operator-valued maps on a compact space, the same argument produces one unit of that map ring and hence continuous pointwise transport and inverse transport."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TransportFormula()
    {
        Formula q = F.Id("q"), s = F.Id("s"), t = F.Id("t"), u = F.Id("u");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, q, F.InMacro, F.Sp, F.Id("TransportData"), F.Comma, F.Sp,
            F.Forall, F.Sp, s, F.InMacro, F.Sp, Call("Parameter", q), F.Comma, F.Sp,
            F.Forall, F.Sp, t, F.InMacro, F.Sp, Call("Parameter", q), F.Comma, F.Sp,
            F.Exists, F.Sp, u, F.InMacro, F.Sp, Call("Units", Call("Ring", q)), F.Comma, F.Sp,
            Call("P", q, t), F.Sp, F.Cdot, F.Sp, u, F.Sp, F.Eq, F.Sp, u, F.Sp, F.Cdot, F.Sp, Call("P", q, s), F.Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
