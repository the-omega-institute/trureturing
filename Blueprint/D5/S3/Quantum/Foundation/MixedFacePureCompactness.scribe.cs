using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class MixedFacePureCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper pure-pair faces and maximal mixed faces close the original pure locus.",
        H("Compactness from maximal mixed faces"), Blocks(
            Describe.Lean(DescribeId.Create("pure-closed-compact-of-mixed-face-coatoms"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/MixedFacePureCompactness.pure_closed_compact_of_mixed_face_coatoms"),
                H("Closedness and compactness of the whole pure locus"),
                StatementSource.FromAuthor(Disp(Telescope(Implies(Hypotheses(),
                    And(Call("IsClosed", Pure()), Call("IsCompact", Pure())))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be a finite-dimensional real normed space, C a closed spanning pointed cone, and u a real linear unit strictly positive on the nonzero elements of C. Write K for the entire normalized base and P for its full extreme-point set. Assume pairProper(C,u), meaning every two distinct points of P generate a proper actual face of K. Assume also that each proper convex extreme subset of K containing a point outside P is maximal among proper convex extreme subsets of K. Then P is closed and compact in V.")),
                    Paragraph(Text("Suppose a sequence in P converges to a mixed point x of the compact base. Fix any pure point q. Eventually the sequence points differ from q. Lift each of their pair faces with q to a proper cone face and take a nonzero linear support, nonnegative on C and zero on that face. Normalize these supports in operator norm. A subsequence converges on the compact dual unit sphere, and joint continuity of evaluation gives a norm-one support e that is nonnegative on C and vanishes at x and q.")),
                    Paragraph(Text("The zero slice of e in K is a proper face by the spanning condition. It contains the entire normalized principal face of x because a nonnegative functional vanishing at x vanishes at every cone vector positively dominated by x. This makes the principal face proper. It is closed, and compact convex generation supplies a pure point q outside it. The proper zero slice for this q would strictly contain the principal face, contradicting maximality. Thus P is closed in the compact base and is compact.")),
                    Paragraph(Text("The all-label Hit route to compactness uses incidence of distinguishable pure neighbours with every pure-pair face. See "),
                        Ref("D5/S3/Quantum/Foundation/HitPureCompactness.hit_pure_closed_compact"), Text(".")),
                    Paragraph(Text("In downstream L2 geometry, closedness of the pure locus is the input used to rule out degeneration of limiting pair ellipsoids in Quantum Origin Binary Normal Differences and Orientation XVII, Theorem 198.6, at source revision 5267f37e2dd8562f3d93ee93d56425d0667626d1."))),
                DescribeRole.Theorem))));

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Base() => Call("base", F.Id("C"), F.Id("u"));
    private static Formula Pure() => Call("pure", F.Id("C"), F.Id("u"));
    private static Formula ProperFace(Formula face) => And(Call("Convex", Real(), face),
        And(Call("IsExtreme", Real(), Base(), face), Rel(face, FormulaRelationOperator.NotEqual, Base())));
    private static Formula MixedCoatoms()
    {
        var set = Call("Set", F.Id("V"));
        var f = F.Id("F");
        var g = F.Id("G");
        var x = F.Id("x");
        var mixed = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("x"), F.Id("V"),
            And(Rel(x, FormulaRelationOperator.MemberOf, f),
                new Formula.Not(Rel(x, FormulaRelationOperator.MemberOf, Pure()))));
        return All("F", set, Implies(And(ProperFace(f), mixed),
            All("G", set, Implies(And(ProperFace(g), Rel(f, FormulaRelationOperator.SubsetOf, g)),
                Rel(g, FormulaRelationOperator.Equal, f)))));
    }
    private static Formula Hypotheses() => And(Call("IsClosed", F.Id("C")), And(
        All("x", F.Id("V"), Implies(And(
            Rel(F.Id("x"), FormulaRelationOperator.MemberOf, F.Id("C")),
            Rel(F.Id("x"), FormulaRelationOperator.NotEqual, D(0))),
            Rel(D(0), FormulaRelationOperator.LessThan, Call("u", F.Id("x"))))),
        And(Rel(Call("span", Real(), F.Id("C")), FormulaRelationOperator.Equal, F.Id("top")),
            And(Call("pairProper", F.Id("C"), F.Id("u")), MixedCoatoms()))));
    private static Formula Telescope(Formula body) => All("V", F.Id("Type"),
        Seq(OpenBracket, Call("NormedAddCommGroup", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", Real(), F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", Real(), F.Id("V")), CloseBracket, Sp,
            All("C", Call("PointedCone", Real(), F.Id("V")),
                All("u", Call("LinearMap", Real(), F.Id("V"), Real()), body))));
}
