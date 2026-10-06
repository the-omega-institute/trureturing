using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class PrefixReversalDoubleInsertionCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two independently specified insertion gaps classify every configuration with the same double-deletion residual up to reversal.",
        H("Double-Insertion Prefix-Reversal Coordinates"),
        Blocks(
            Paragraph(Text(
                "Configurations at dimension m+2 assign labels to positions bijectively. Choose an actual tuple z "
                + "whose penultimate and last labels are t and s. Its double-deletion residual P is obtained by "
                + "deleting s and then t from its oriented circular tuple. DoubleStar(t,s,P) consists of all "
                + "configurations having residual P or its reverse. This domain is specified independently of "
                + "a path or its scanned support. The labels t and s differ because z is a permutation.")),
            Describe.Lean(DescribeId.Create("double-insertion-coordinates"),
                DeclarationHandle.Create(Prefix + "doubleInsertion_coordinates_bijective"),
                H("The Independent Two-Gap Bijection"),
                StatementSource.FromAuthor(CoordinateFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For m at least three the configurations in DoubleStar(t,s,P) are in bijection with "
                        + "Fin(m) times Fin(m+1) times Fin(m+2) times Bool. The first coordinate chooses the "
                        + "gap of t among the residual labels; the second chooses the gap of s among the resulting "
                        + "m+1 labels. The remaining coordinates specify the rotation and reflection of the actual "
                        + "tuple. Consequently this independently defined domain has 2m(m+1)(m+2) elements.")),
                    Paragraph(Text(
                        "Let a, b and c reverse the first m+2, m+1 and m positions. The coordinate operation d "
                        + "reverses the first m-1 positions. The product cd rotates the first m residual labels "
                        + "and fixes t,s. Thus the outer anchors are z(cd)^k and their current circles after deleting "
                        + "s are (rotate_k(R),t), where R is the first m labels of z. Within each current circle "
                        + "the native single-deletion coordinates give z(cd)^k(bc)^l(ab)^r, followed by a when "
                        + "the Bool coordinate is true. The operation d describes coordinates only.")),
                    Paragraph(Text(
                        "To find a coordinate for an arbitrary configuration, first rotate its full tuple to "
                        + "put s last, then rotate its first m+1 positions to put t penultimate. Its remaining "
                        + "m-label tuple has circular residual P or its reverse. Reverse this block in the latter "
                        + "case, then compare rotations with R. This gives an outer anchor and the fixed-current-circle "
                        + "coordinates give the other three coordinates. For uniqueness, the successor of t in the "
                        + "current circle determines its outer gap. Two outer current circles cannot be reverses: "
                        + "deleting t would make the nodup residual P equal to its reverse, which is impossible "
                        + "on at least three labels. The inner native-coordinate bijection then determines the rest."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-equivalence"),
                DeclarationHandle.Create(Prefix + "doubleInsertionCoordinateEquiv"),
                H("The Coordinate Equivalence"),
                StatementSource.FromAuthor(CoordinateFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bijective actual coordinate map defines an equivalence between the four coordinate factors "
                    + "and the independent double-deletion subtype. Its forward map is doubleInsertionMap, and its "
                    + "inverse recovers the unique insertion gaps, cyclic position and reflection direction. "
                    + "This equivalence transports the independently measured finite domain to native coordinates."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "The coordinate bijection classifies a double-deletion domain. Constructing a generator cycle "
                + "on this domain additionally requires actual component paths and converting edges.")))));

    private static Formula CoordinateFormula(bool asEquivalence)
    {
        Formula m = F.Id("m"), z = F.Id("z");
        Formula n = Add(m, D(2));
        Formula labels = Call("Fin", n);
        Formula t = Call("apply", z, Call("penultimatePosition", m));
        Formula s = Call("apply", z, Call("lastPosition", Add(m, D(1))));
        Formula p = Call("delete", t, Call("delete", s, Call("configurationCycle", z)));
        Formula coordinates = Call("Product", Call("Fin", m),
            Call("Product", Call("Fin", Add(m, D(1))),
                Call("Product", labels, Call("Bool"))));
        Formula domain = Call("Subtype", Call("DoubleStar", t, s, p));
        Formula conclusion = asEquivalence ? Call("Equiv", coordinates, domain)
            : Call("Bijective", Call("doubleInsertionMap", z));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", Call("Configuration", Add(m, D(1))), conclusion))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
}
