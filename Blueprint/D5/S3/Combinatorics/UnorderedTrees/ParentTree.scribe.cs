using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class ParentTreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/ParentTree.";
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula CallQualified(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified(owner, name), [.. arguments]);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite rooted parent trees admit unordered vertex isomorphisms. Their vertex-height and internal-vertex count descend to the finite isomorphism quotient.",
        H("Actual unordered rooted trees"),
        Blocks(
            Node("tree", "Rooted parent trees", "Tree", TreeFormula(),
                "A tree is a parent map on its original vertices with a distinguished fixed root and a proof that every vertex reaches that root after finitely many parent steps. The child relation omits the artificial root loop, and child fibres are unordered.", DescribeRole.Definition),
            Node("iso", "Actual vertex isomorphisms", "Iso", IsoFormula(),
                "An isomorphism is a bijection of the complete original vertex carriers that sends the root to the root and commutes with every parent edge.", DescribeRole.Definition),
            Node("iso-symm", "Symmetry of rooted isomorphisms", "Iso.symm", HasType(CallQualified("Iso", "symm", E), Call("Iso", S, T)),
                "The inverse vertex equivalence reverses the root and parent-preservation equations.", DescribeRole.Definition),
            Node("iso-trans", "Composition of rooted isomorphisms", "Iso.trans", HasType(CallQualified("Iso", "trans", E, F.Id("f")), Call("Iso", T, F.Id("R"))),
                "Composition composes the carrier equivalences and the two root-preserving parent-map equations.", DescribeRole.Definition),
            Node("relabel", "Relabelling a parent tree", "relabel", RelabelFormula(),
                "Relabelling transports the parent map and root along an equivalence of vertex labels. Reaching the root is transported by iterate semiconjugacy.", DescribeRole.Definition),
            Node("relabel-iso", "The canonical relabelling isomorphism", "relabelIso", HasType(Call("relabelIso", T, E), Call("Iso", T, Call("relabel", T, E))),
                "The relabelling equivalence is itself a rooted vertex isomorphism.", DescribeRole.Definition),
            Node("child", "The nonroot child relation", "Child",
                Iff(Call("Child", F.Id("T"), F.Id("v"), F.Id("w")),
                    And(Ne(F.Id("v"), Call("root", F.Id("T"))), Eqn(Call("parent", F.Id("T"), F.Id("v")), F.Id("w")))),
                "Child excludes the fixed root loop and records exactly one parent edge.", DescribeRole.Definition),
            Node("internal", "Internal vertices", "Internal",
                Iff(Call("Internal", F.Id("T"), F.Id("v")),
                    Some("w", F.Id("V"), Call("Child", F.Id("T"), F.Id("w"), F.Id("v")))),
                "An internal vertex has an actual nonroot child.", DescribeRole.Definition),
            Node("depth", "Vertex depth", "depth", Eqn(Call("depth", T, X), Seq(
                    new Formula.Subscript(Min, Seq(K, Sp, Mid, Sp, Eqn(Iterate(T, K, X), Root(T)))))),
                "Depth is the least natural iterate index at which the parent map reaches the fixed root.", DescribeRole.Definition),
            Node("depth-reaches", "The depth iterate reaches the root", "reaches_depth",
                Eqn(Call("iterate", Call("parent", F.Id("T")), Call("depth", F.Id("T"), F.Id("v")), F.Id("v")), Call("root", F.Id("T"))),
                "The parent iterate at depth(v) reaches the root by the defining least-hitting-time witness.", DescribeRole.Theorem),
            Node("depth-minimum", "Minimality of the depth", "depth_le",
                Imp(Eqn(Call("iterate", Call("parent", F.Id("T")), F.Id("k"), F.Id("v")), Call("root", F.Id("T"))), Le(Call("depth", F.Id("T"), F.Id("v")), F.Id("k"))),
                "Every iterate reaching the root has index at least the depth.", DescribeRole.Theorem),
            Node("depth-root", "The root has depth zero", "depth_root",
                Eqn(Call("depth", F.Id("T"), Call("root", F.Id("T"))), D(0)),
                "The zero iterate already reaches the root when the starting vertex is the root.", DescribeRole.Theorem),
            Node("depth-parent", "The nonroot depth step", "depth_parent",
                Imp(Ne(F.Id("v"), Call("root", F.Id("T"))), Eqn(Call("depth", F.Id("T"), F.Id("v")), Seq(Call("depth", F.Id("T"), Call("parent", F.Id("T"), F.Id("v"))), Sp, Plus, Sp, D(1)))),
                "Every nonroot vertex is one level deeper than its parent.", DescribeRole.Theorem),
            Node("iso-child", "Isomorphisms preserve child edges", "iso_child",
                Iff(Call("Child", F.Id("T"), F.Id("a"), F.Id("b")), Call("Child", F.Id("S"), Image(F.Id("a")), Image(F.Id("b")))),
                "Root preservation and parent commutation preserve and reflect the actual child relation.", DescribeRole.Theorem),
            Node("code", "The whole-carrier branch-code classifier", "code_eq_iff_iso",
                Iff(Eqn(Call("branchCode", Call("parent", F.Id("T")), Call("root", F.Id("T"))), Call("branchCode", Call("parent", F.Id("S")), Call("root", F.Id("S")))), Call("Nonempty", Call("Iso", F.Id("T"), F.Id("S")))),
                "The existing transient-tree classifier applies to the complete original carrier after the root descendant bridge. Restricting a parent-map isomorphism gives the reverse direction.", DescribeRole.Theorem),
            Node("iso-depth", "Isomorphisms preserve depth", "iso_depth",
                Eqn(Call("depth", F.Id("S"), Image(X)), Call("depth", F.Id("T"), F.Id("v"))),
                "Iterate semiconjugacy and root preservation identify the two least hitting times.", DescribeRole.Theorem),
            Node("iso-internal", "Isomorphisms preserve internality", "iso_internal",
                Iff(Call("Internal", F.Id("T"), F.Id("v")), Call("Internal", F.Id("S"), Image(X))),
                "The child-edge equivalence transports the existence of an actual child.", DescribeRole.Theorem),
            Node("internal-equiv", "The internal-vertex equivalence", "internalEquiv", HasType(Call("internalEquiv", E), Equivalent(Core(T, V), Core(S, F.Id("W")))),
                "The carrier equivalence restricts to the subtypes of internal vertices.", DescribeRole.Definition),
            Node("height", "Vertex-height", "height",
                Eqn(Call("height", T), Seq(
                    new Formula.Subscript(Max, Mem(X, V)), Sp, Call("depth", T, X), Plus, D(1))),
                "Vertex-height is one plus the maximum depth over the finite original carrier.", DescribeRole.Definition),
            Node("internal-count", "Internal-vertex count", "internalCount", Eqn(Call("internalCount", T), Call("card", Core(T, V))),
                "The count is the finite cardinality of the subtype of original internal vertices.", DescribeRole.Definition),
            Node("iso-height", "Isomorphisms preserve vertex-height", "iso_height",
                Eqn(Call("height", F.Id("T")), Call("height", F.Id("S"))),
                "The depth equivalence transports the finite maximum across the carrier equivalence.", DescribeRole.Theorem),
            Node("tree-setoid", "The parent-data setoid", "treeSetoid", Iff(Apply(Seq(Call("treeSetoid", N), Dot, F.Id("r")), T, S),
                    Eqn(Call("branchCode", Parent(T), Root(T)), Call("branchCode", Parent(S), Root(S)))),
                "On parent data over Fin n, the relation is equality of complete branch codes with the chosen root.", DescribeRole.Definition),
            Node("tree-class", "The actual unordered class carrier", "TreeClass", Eqn(Call("TreeClass", N), Call("Quotient", Call("treeSetoid", N))),
                "TreeClass is the quotient of all rooted parent data on Fin n by the full root- and parent-preserving vertex-isomorphism relation.", DescribeRole.Definition),
            Node("fintype-tree", "Finiteness of parent data", "fintype_tree", HasType(Call("fintypeTree", N), Call("Fintype", Call("Tree", Call("Fin", N)))),
                "The finite parent map and root data on Fin n form a finite type.", DescribeRole.Definition),
            Node("fintype-classes", "Finiteness of unordered classes", "fintype_classes", HasType(Call("fintypeClasses", N), Call("Fintype", Call("TreeClass", N))),
                "The quotient carrier inherits a finite type from the finite parent-data carrier.", DescribeRole.Definition),
            Node("class-height", "Class vertex-height", "classHeight", Eqn(Call("classHeight", Class(T)), Call("height", T)),
                "Vertex-height descends to the quotient because actual vertex isomorphisms preserve it.", DescribeRole.Definition),
            Node("class-internal-count", "Class internal-vertex count", "classInternalCount", Eqn(Call("classInternalCount", Class(T)), Call("internalCount", T)),
                "Internal-vertex count descends to the quotient through the internal subtype equivalence.", DescribeRole.Definition),
            Node("count", "The counting sequence", "a",
                Eqn(Call("a", N), Call("card", Subtype(T, Call("TreeClass", N),
                    Eqn(Call("classHeight", T), Call("classInternalCount", T))))),
                "The sequence counts the actual size-n unordered rooted-tree classes whose vertex-height equals their internal-vertex count. The defining subtype predicate is stated in the source result and preserved by the class observables.", DescribeRole.Definition))));

    private static Formula T => F.Id("T");
    private static Formula S => F.Id("S");
    private static Formula Image(Formula x) => Apply(Seq(E, Dot, F.Id("equiv")), x);
    private static Formula V => F.Id("V");
    private static Formula E => F.Id("e");
    private static Formula X => F.Id("v");
    private static Formula K => F.Id("k");
    private static Formula N => F.Id("n");
    private static Formula Root(Formula tree) => Call("root", tree);
    private static Formula Parent(Formula tree) => Call("parent", tree);
    private static Formula Iterate(Formula tree, Formula index, Formula vertex) =>
        Call("iterate", Parent(tree), index, vertex);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula HasType(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equivalent, right);
    private static Formula Subtype(Formula value, Formula type, Formula condition) =>
        Seq(OpenBrace, HasType(value, type), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Core(Formula tree, Formula vertices) =>
        Subtype(X, vertices, Call("Internal", tree, X));
    private static Formula Class(Formula tree) => Seq(OpenBracket, tree, CloseBracket);
    private static Formula TreeFormula() => new Formula.Aligned([
        Seq(Amp, HasType(T, Call("Tree", V))),
        Seq(Amp, HasType(Parent(T), new Formula.TypeArrow(V, V))),
        Seq(Amp, HasType(Root(T), V)),
        Seq(Amp, Eqn(Apply(Parent(T), Root(T)), Root(T))),
        Seq(Amp, All("v", V, Some("k", Nat, Eqn(Iterate(T, K, X), Root(T)))))
    ]);
    private static Formula IsoFormula()
    {
        var image = Seq(E, Dot, F.Id("equiv"));
        return new Formula.Aligned([
            Seq(Amp, HasType(E, Call("Iso", T, S))),
            Seq(Amp, HasType(image, Equivalent(V, F.Id("W")))),
            Seq(Amp, Eqn(Apply(image, Root(T)), Root(S))),
            Seq(Amp, All("v", V, Eqn(Apply(image, Apply(Parent(T), X)), Apply(Parent(S), Apply(image, X)))))
        ]);
    }
    private static Formula RelabelFormula()
    {
        var relabelled = Call("relabel", T, E);
        var w = F.Id("w");
        var inverse = Seq(E, Dot, F.Id("symm"));
        return new Formula.Aligned([
            Seq(Amp, Eqn(Root(relabelled), Apply(E, Root(T)))),
            Seq(Amp, All("w", F.Id("W"), Eqn(Apply(Parent(relabelled), w),
                Apply(E, Apply(Parent(T), Apply(inverse, w))))))
        ]);
    }

    private static Formula Parameter(string name, Formula type) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type));
    private static Formula Finite(Formula carrier) =>
        Seq(OpenBracket, Call("Fintype", carrier), CloseBracket);
    private static Formula For(Formula body, params Formula[] parameters) =>
        Seq(Forall, Sp, Seq(parameters.Select(parameter => Seq(parameter, Sp)).ToArray()), Comma, Sp,
            Parenthesized(body));

    private static Formula Scope(string name, Formula body)
    {
        var w = F.Id("W");
        var z = F.Id("Z");
        var vType = Parameter("V", F.Id("Type"));
        var wType = Parameter("W", F.Id("Type"));
        var tree = Parameter("T", Call("Tree", V));
        var other = Parameter("S", Call("Tree", w));
        var iso = Parameter("e", Call("Iso", T, S));
        var vertex = Parameter("v", V);
        var n = Parameter("n", Nat);
        return name switch
        {
            "Tree" => For(body, vType, tree),
            "Iso" or "Iso.symm" or "internalEquiv" => For(body, vType, wType, tree, other, iso),
            "Iso.trans" => For(body, vType, wType, Parameter("Z", F.Id("Type")), tree, other,
                Parameter("R", Call("Tree", z)), iso, Parameter("f", Call("Iso", S, F.Id("R")))),
            "relabel" or "relabelIso" => For(body, vType, wType, tree, Parameter("e", Equivalent(V, w))),
            "Child" => For(body, vType, tree, vertex, Parameter("w", V)),
            "Internal" or "depth" or "reaches_depth" or "depth_parent" => For(body, vType, tree, vertex),
            "depth_le" => For(body, vType, tree, vertex, Parameter("k", Nat)),
            "depth_root" => For(body, vType, tree),
            "iso_child" => For(body, vType, wType, tree, other, iso, Parameter("a", V), Parameter("b", V)),
            "iso_depth" or "iso_internal" => For(body, vType, wType, tree, other, iso, vertex),
            "code_eq_iff_iso" => For(body, vType, wType, Finite(V), Finite(w), tree, other),
            "iso_height" => For(body, vType, wType, Finite(V), Finite(w), tree, other, iso),
            "height" or "internalCount" => For(body, vType, Finite(V), tree),
            "treeSetoid" => For(body, n, Parameter("T", Call("Tree", Call("Fin", N))),
                Parameter("S", Call("Tree", Call("Fin", N)))),
            "classHeight" or "classInternalCount" => For(body, n, Parameter("T", Call("Tree", Call("Fin", N)))),
            _ => For(body, n)
        };
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("parent-tree-" + id), DeclarationHandle.Create(Owner + declaration.Split('.')[^1]), H(title),
        StatementSource.FromAuthor(Disp(Scope(declaration, formula))), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
}
