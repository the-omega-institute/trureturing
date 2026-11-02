using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class PerpHyperplaneHexagonContextualityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/saniga2025hexagons");

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Binary => At(Qualified("ZMod"), D(2));
    private static Formula Point => Local("point");
    private static Formula PointSet => At(Qualified("Finset"), Point);
    private static Formula LineSet => At(Qualified("Finset"), PointSet);
    private static Formula Assignment => Arrow(Point, Binary);
    private static Formula Subspace => At(Qualified("Submodule"), Binary, Point);
    private static Formula MatrixType => At(Qualified("Matrix"),
        Arrow(At(Qualified("Fin"), D(3)), At(Qualified("Fin"), D(2))),
        Arrow(At(Qualified("Fin"), D(3)), At(Qualified("Fin"), D(2))), Complexes);
    private static Formula ZeroBinary => Typed(D(0), Binary);
    private static Formula C => X("c");
    private static Formula HSet => X("h");
    private static Formula L => X("l");
    private static Formula M => X("m");
    private static Formula Q => X("q");
    private static Formula W => Local("w");

    private static Formula PointDefinition => Equal(Local("point"), Arrow(
        At(Qualified("Fin"), D(3)), Parenthesized(Seq(Binary, Sp, Times, Sp, Binary))));

    private static Formula SpaceDefinition => Equal(Typed(W, Subspace),
        Typed(Qualified("Top", "top"), Subspace));

    private static Formula SignDefinition => All("l", PointSet,
        Equal(Typed(LocalCall("lineSign", L), Binary), At(Qualified("ite"),
            Equal(OwnerCall("lineProduct", L), new Formula.Negate(Typed(D(1), MatrixType))),
            Typed(D(1), Binary), ZeroBinary)));

    private static Formula ViolationsDefinition => All("c", LineSet, All("f", Assignment,
        Equal(Typed(LocalCall("violations", C, X("f")), Naturals),
            Card(At(Qualified("Finset", "filter"),
                LambdaOf("l", PointSet, NotEqual(
                    SumIn("q", Point, L, At(X("f"), Q)), LocalCall("lineSign", L))), C)))));

    private static Formula DegreeDefinition => All("c", LineSet,
        Equal(Typed(LocalCall("contextualityDegree", C), Naturals),
            At(Qualified("sInf"), At(Qualified("Set", "range"),
                Typed(LocalCall("violations", C), Arrow(Assignment, Naturals))))));

    private static Formula NoTriangle
    {
        get
        {
            Formula body = Qualified("False");
            Formula[] hypotheses =
            [
                NotEqual(X("a"), X("b")), NotEqual(X("b"), C), NotEqual(C, X("a")),
                NotEqual(L, M), NotEqual(M, X("n")), NotEqual(X("n"), L),
                Member(X("a"), L), Member(X("b"), L), Member(X("b"), M),
                Member(C, M), Member(C, X("n")), Member(X("a"), X("n")),
            ];
            for (var i = hypotheses.Length - 1; i >= 0; i--) body = Imp(hypotheses[i], body);
            return All("a", Point, All("b", Point, All("c", Point,
                AllIn("l", PointSet, HSet, AllIn("m", PointSet, HSet,
                    AllIn("n", PointSet, HSet, body))))));
        }
    }

    private static Formula Planarity => All("z", Point, All("a", Point, All("b", Point,
        AllIn("l", PointSet, HSet, AllIn("m", PointSet, HSet,
            Imp(Member(X("z"), L), Imp(Member(X("z"), M), Imp(Member(X("a"), L),
                Imp(Member(X("b"), M), Equal(OwnerCall("B", X("a"), X("b")), ZeroBinary))))))))));

    private static Formula HexagonDefinition => All("h", LineSet,
        Equal(Typed(LocalCall("IsClassicalHexagon", HSet), Qualified("Prop")),
            And(SubsetOf(HSet, OwnerCall("lines", W)),
                And(AllIn("q", Point, OwnerCall("points", W),
                        Equal(Card(At(Qualified("Finset", "filter"),
                            LambdaOf("l", PointSet, Member(Q, L)), HSet)), Typed(D(3), Naturals))),
                    And(NoTriangle, Planarity)))));

    private static Formula ClaimBody => All("c", LineSet,
        Imp(SubsetOf(C, OwnerCall("lines", W)),
            Imp(LT(Typed(D(0), Naturals), LocalCall("contextualityDegree", C)),
                Some("h", LineSet, And(LocalCall("IsClassicalHexagon", HSet),
                    Equal(LocalCall("contextualityDegree", C), Card(Intersection(C, HSet))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The IIZ perp hyperplane refutes the classical-hexagon contextuality generalization.",
        H("A perp hyperplane and classical hexagon intersections"),
        Blocks(
            Definition("point", "Three-qubit binary labels", "point", PointDefinition,
                AssessedProvenance.FromLiterature(Source),
                "A label assigns a pair of binary coordinates to each of three qubits. "
                + "The pair gives the X and Z exponents, with the pair (1,1) represented by Y = iXZ. "
                + "The zero label represents the identity and is included in this type. "
                + "The map in main.tex, lines 213–222, lists the Z coordinates before the X coordinates; "
                + "here the coordinates are grouped by qubit with X first. The projective points are the nonzero labels, as in lines 222–233."),
            Definition("w", "The full binary symplectic space", "w", SpaceDefinition,
                AssessedProvenance.FromLiterature(Source),
                "The submodule w is the whole space of three-qubit labels. Its nonzero "
                + "vectors are the 63 points of W(5,2), and its isotropic triples are the lines. "
                + "This is the ambient space of main.tex, lines 222–233 and 736–740."),
            Definition("line-sign", "Additive Pauli product signs", "lineSign", SignDefinition,
                AssessedProvenance.FromLiterature(Source),
                "The value is one in ZMod 2 when the matrix product of l is minus the "
                + "identity matrix, and zero otherwise. The definition applies to every finite "
                + "set of labels; for a line it is the binary valuation of its context sign "
                + "in main.tex, lines 346–349. The displayed identity is a matrix identity "
                + "on the three-qubit space, rather than a complex scalar."),
            Definition("violations", "Unsatisfied contexts of an assignment", "violations", ViolationsDefinition,
                AssessedProvenance.FromLiterature(Source),
                "For a binary assignment f, count the members l of c for which the sum of "
                + "the assigned values differs from the additive Pauli sign. Binary addition "
                + "encodes multiplication of signs, with zero representing plus one. "
                + "This is the count of unsatisfied contexts in main.tex, lines 341–355. "
                + "The cardinality takes values in the natural numbers without a cast."),
            Definition("contextuality-degree", "Minimum violation count", "contextualityDegree", DegreeDefinition,
                AssessedProvenance.FromLiterature(Source),
                "Take the natural infimum of the range of violation counts over all binary "
                + "assignments on the label type. This is a nonempty finite set of attainable "
                + "counts, so its infimum is its minimum. The value at the zero label has "
                + "no effect on a family of lines. This expresses the contextuality degree "
                + "and incidence-matrix Hamming distance of main.tex, lines 341–352."),
            Definition("classical-hexagon", "The hexagon incidence and planarity conditions", "IsClassicalHexagon",
                HexagonDefinition, AssessedProvenance.FromRepo(Source),
                "The finite family h consists of isotropic lines, with exactly three lines "
                + "through each nonzero point. Three distinct points cannot be joined cyclically "
                + "by three distinct lines of h. Whenever two lines of h pass through the same "
                + "point z, every point a on the first is orthogonal to every point b on the second. "
                + "These are the incidence, absence-of-triangles and planarity conditions used here. "
                + "Every classical embedding in main.tex, lines 289–300 and 477–479, satisfies them; "
                + "the predicate does not assert a characterization of all such embeddings."),
            Definition("claim", "The equality proposed for arbitrary contextual line families", "claim",
                Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(ClaimBody)),
                AssessedProvenance.FromRepo(Source),
                "Every finite family c of isotropic lines with positive contextuality degree "
                + "would have the same degree as the natural number of its lines shared with "
                + "some h satisfying the hexagon conditions. This is the line-family reading "
                + "of the generalization in main.tex, lines 736–740. "
                + "The next paragraph, lines 742–744, includes the complement of a skew hexagon "
                + "among the subgeometries to which that generalization is applied."),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The perp hyperplane contradicts the equality"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let C be the family of all isotropic lines whose points commute with IIZ, "
                        + "and let S be the nonzero labels commuting with IIZ. "
                        + "There are 63 nonzero labels in the whole space and 31 in S. "
                        + "Enumerate the triples generated by distinct orthogonal labels u and v "
                        + "in S for which the sum of the three single-qubit multiplication exponents "
                        + "is two in ZMod 4. There are twelve distinct triples in this enumeration.")),
                    Paragraph(Text(
                        "Every isotropic line has the form {u,v,u+v} for distinct nonzero "
                        + "orthogonal u and v, and every such set of three points is a line. The multiplication "
                        + "phase of u and v is the additive character of their total multiplication residue "
                        + "in ZMod 4. That character takes the value minus one exactly at two. "
                        + "The product of the three observables is the phase times the identity matrix, so a line "
                        + "of C is negative exactly when it is one of the twelve enumerated triples. "
                        + "Double counting incidences between any line family and any point set "
                        + "equates the sum of intersection sizes over lines with the sum of "
                        + "line degrees over points. Each isotropic line meets S in three points "
                        + "if it belongs to C and in one point otherwise: the binary form on "
                        + "u, v and u+v gives precisely these two possibilities. "
                        + "Applying the incidence identity to all 63 points, with three points "
                        + "per line and three lines through each point, shows that every h "
                        + "satisfying the hexagon conditions has 63 lines.")),
                    Paragraph(Text(
                        "The six triples {XII,IXI,XXI}, {IZI,ZII,ZZI}, {XZI,ZXI,YYI}, "
                        + "{XII,IZI,XZI}, {IXI,ZII,ZXI} and {XXI,ZZI,YYI} all lie in C. "
                        + "Map the nine row-major labels to the square in RankOfContextualityNonPowerTwo. "
                        + "Convert an assignment value to true exactly when it is one in ZMod 2. "
                        + "The frozen Square.parity_miss gives a context whose Boolean parity differs "
                        + "from its target; Square.bv_parity identifies that parity with the binary sum. "
                        + "The Pauli sign agrees with the target, since only the last context is negative. "
                        + "Thus every assignment violates at least one of these six lines, and the "
                        + "contextuality degree of C is positive. The constant zero assignment "
                        + "violates exactly the twelve negative lines, giving degree at most twelve.")),
                    Paragraph(Text(
                        "Now count incidences between h and S. Each of the 31 points of S "
                        + "lies on three lines of h, giving 93 incidences. Write k for the "
                        + "natural cardinality of C intersect h. The k lines contained in S "
                        + "contribute three incidences each, while the other 63 minus k lines "
                        + "contribute one each. Hence 93 = 2k + 63, which gives at least fifteen "
                        + "shared lines. Applying the asserted equality to C would identify "
                        + "its degree, at most twelve, with this intersection cardinality, "
                        + "at least fifteen. The resulting natural-number inequalities contradict "
                        + "each other. The argument uses only the line and degree conditions "
                        + "of h, so it also applies when the triangle and planarity conditions "
                        + "are retained."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("saniga-et-al-2025-hexagon-contextuality-generalization"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string title, string declaration,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Contextuality",
        "PerpHyperplaneHexagonContextualityRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula OwnerCall(string name, params Formula[] arguments) => At(Qualified(
        "D5", "S3", "Quantum", "Contextuality", "LinearDoilyNegativeLineParity", name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula AllIn(string name, Formula type, Formula set, Formula body) =>
        All(name, type, Imp(Member(X(name), set), body));
    private static Formula Card(Formula set) => Typed(At(Qualified("Finset", "card"), set), Naturals);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula SubsetOf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Intersection(Formula left, Formula right) =>
        At(Qualified("Finset", "inter"), left, right);
    private static Formula SumIn(string name, Formula type, Formula set, Formula body) =>
        At(Qualified("Finset", "sum"), set, LambdaOf(name, type, body));
}
