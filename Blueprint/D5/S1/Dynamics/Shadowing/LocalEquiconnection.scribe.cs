using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LocalEquiconnectionDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma, Sp);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula SphereFormula() => Seq(
        All("V", Id("RealNormedSpace")),
        Call("sphere", Id("V")), Sp, Eq, Sp,
        Call("LocalConnectorData", Call("NonantipodalPairs", Call("UnitSphere", Id("V"))),
            Seq(Open, Id("p"), Comma, Id("q"), Comma, Id("s"), Close, Sp, Mapsto, Sp,
                Call("normalize", Seq(Open, D(1), Minus, Id("s"), Close, Id("p"), Plus, Id("s"), Id("q"))))));
    private static Formula TransportFormula() => Seq(
        All("X", Id("TopologicalSpace")), All("Y", Id("TopologicalSpace")),
        All("e", Call("Homeomorphism", Id("X"), Id("Y"))),
        All("H", Call("LocalEquiconnection", Id("Y"))),
        Call("transport", Id("e"), Id("H")), Sp, Eq, Sp,
        Call("LocalConnectorData", Call("PairDomainPullback", Id("e"), Id("H")),
            Seq(Open, Id("p"), Comma, Id("q"), Comma, Id("s"), Close, Sp, Mapsto, Sp,
                Call("inverse", Id("e"), Call("connect", Id("H"), Call("e", Id("p")), Call("e", Id("q")), Id("s"))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized nonantipodal chords provide coherent local equiconnections on normed unit spheres and transport through homeomorphisms.",
        H("Explicit Sphere Local Equiconnections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-sphere-connector"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/LocalEquiconnection.sphere"),
                H("Normalized straight interpolation"),
                StatementSource.FromAuthor(SphereFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the subtype sphere of radius one in any real normed space, use the open "
                    + "domain of pairs (p,q) with q≠-p. The connector normalizes (1-s)p+sq for "
                    + "s in [0,1]. Unit norms show that a zero chord would force s=1/2 and q=-p, "
                    + "so normalization is continuous throughout the stated domain. It has both "
                    + "endpoint identities and fixes every diagonal pair for every parameter. "
                    + "Finite dimensionality is unnecessary for this connector data."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("homeomorphism-connector-transport"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/LocalEquiconnection.transport"),
                H("Transport the domain and connector together"),
                StatementSource.FromAuthor(TransportFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A homeomorphism e:X→Y pulls back the open pair domain and sends the connector "
                    + "output through e inverse. The continuity and all three identities are "
                    + "transported as data. Applying this to a homeomorphism onto a Euclidean unit "
                    + "sphere supplies genuine topological-sphere data without differentiability "
                    + "or any compatibility between e, the connector and the dynamical map. "
                    + "No compact LEC implies ANR assertion is made."))),
                DescribeRole.Definition))));
}
