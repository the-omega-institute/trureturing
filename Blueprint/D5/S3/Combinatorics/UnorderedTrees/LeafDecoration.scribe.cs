using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class LeafDecorationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.";
    private static Formula T => F.Id("T");
    private static Formula S => F.Id("S");
    private static Formula V => F.Id("V");
    private static Formula P => F.Id("p");
    private static Formula K => F.Id("k");
    private static Formula E => F.Id("e");
    private static Formula Hr => F.Id("hr");
    private static Formula Hs => F.Id("hs");
    private static Formula Hk => F.Id("hk");
    private static Formula InflatedTree => Call("inflate", T, K);
    private static Formula CoreIso => Call("Iso", Call("prune", T, Hr), Call("prune", S, Hs));
    private static Formula FibreEquality => All("p", Call("Core", T),
        Equal(Card(Call("LeafFibre", T, P)), Card(Call("LeafFibre", S, Image(E, P)))));
    private static Formula PositiveTips => All("p", V, new Formula.Logic(
        new Formula.Not(Call("Internal", T, P)), FormulaLogicOperator.Implies,
        Less(D(0), Apply(K, P))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal subtrees with matching original leaf fibres determine an actual rooted isomorphism.",
        H("Reconstructing a rooted tree from its leaf fibres"),
        Blocks(
            Definition("core", "Core", "The internal vertex carrier",
                Equal(Call("Core", T), Subtype("p", V, Call("Internal", T, P))),
                "The core is the subtype of the original vertex carrier selected by the internal predicate."),
            Definition("fibre", "LeafFibre", "The original leaf fibre",
                Equal(Call("LeafFibre", T, P), Subtype("x", V,
                    new Formula.Logic(new Formula.Not(Call("Internal", T, F.Id("x"))),
                        FormulaLogicOperator.And, Call("Child", T, F.Id("x"), Value(P))))),
                "The fibre consists of the original leaf children of the internal vertex p."),
            Definition("finite-fibre", "instFintypeLeafFibre", "A finite leaf fibre",
                HasType(Call("instFintypeLeafFibre", T, P), Call("Fintype", Call("LeafFibre", T, P))),
                "On a finite original vertex type, restricting to the leaf-child predicate supplies the Fintype instance."),
            Theorem("extend", "extendIso", "Extension of the specified core isomorphism",
                Roots(Binder(Forall, "e", CoreIso,
                    Imp(FibreEquality, Binder(Exists, "f", Call("Iso", T, S),
                        All("p", Call("Core", T), Equal(Image(F.Id("f"), Value(P)), Value(Image(E, P)))))))),
                "Combine the given isomorphism on the cores with chosen bijections on the corresponding leaf fibres. The resulting isomorphism sends each original internal vertex where the specified core map sends it."),
            Theorem("iso-iff-fibres", "iso_iff_fibres", "Restriction and extension of rooted isomorphisms",
                Roots(new Formula.Logic(Call("Nonempty", Call("Iso", T, S)), FormulaLogicOperator.Iff,
                    Parenthesized(Binder(Exists, "e", CoreIso, FibreEquality)))),
                "An actual isomorphism restricts to the pruned cores and original leaf fibres. Conversely, every original vertex belongs to the core or is a leaf over its unique internal parent. The specified core map and fibre bijections preserve every parent edge and the root."),
            Definition("inflated", "Inflated", "The inflated vertex carrier",
                Equal(Call("Inflated", K), Call("Sum", V, Seq(Sigma, Sp, P, Colon, Sp, V, Comma, Sp, Call("Fin", Apply(K, P))))),
                "The carrier consists of the old vertices and a fresh copy of Fin(k(p)) at each old vertex p."),
            Definition("inflate", "inflate", "Attaching fresh leaves",
                new Formula.Aligned([
                    Seq(Amp, HasType(InflatedTree, Call("Tree", Call("Inflated", K)))),
                    Seq(Amp, Equal(Call("root", InflatedTree), Call("inl", Call("root", T)))),
                    Seq(Amp, Binder(Forall, "p", V, Equal(Call("parent", InflatedTree, Call("inl", P)),
                        Call("inl", Call("parent", T, P))))),
                    Seq(Amp, Binder(Forall, "p", V, Binder(Forall, "i", Call("Fin", Apply(K, P)),
                        Equal(Call("parent", InflatedTree, Call("inr", Pair(P, F.Id("i")))),
                            Call("inl", P)))))
                ]),
                "Old vertices retain their old parent edges. Each fresh leaf points to its fibre index, and the root is the image of the old root."),
            Theorem("internal-inflate", "internal_inflate", "The old vertices become internal",
                Binder(Forall, "hk", Parenthesized(PositiveTips),
                    All("p", V, Call("Internal", InflatedTree, Call("inl", P)))),
                "An old internal vertex keeps its old child. At an old terminal, a positive leaf multiplicity supplies a fresh child."),
            Definition("recover", "pruneInflateIso", "Pruning recovers the skeleton",
                Binder(Forall, "hk", Parenthesized(PositiveTips),
                    HasType(Call("pruneInflateIso", T, K, Hk), Call("Iso", T,
                        Call("prune", InflatedTree, Apply(new Formula.Subscript(
                            Seq(Operatorname, Grp(F.Id("internal"))), Seq(Mathrm, Grp(F.Id("inflate")))),
                            T, K, Hk, Call("root", T)))))),
                "The isomorphism uses the left injection. The proof supplied to prune is internal_inflate at the original root, and the pruned carrier excludes every fresh leaf."),
            Definition("recover-fibre", "inflateLeafIso", "The prescribed multiplicity of each fibre",
                Binder(Forall, "hk", Parenthesized(PositiveTips), All("p", V,
                    HasType(Call("inflateLeafIso", T, K, Hk, P),
                        EquivOf(Call("Fin", Apply(K, P)), Call("LeafFibre", InflatedTree,
                            Image(Call("pruneInflateIso", T, K, Hk), P)))))),
                "The equivalence sends an index i to the fresh leaf tagged by (p,i) and extracts that index from the corresponding leaf fibre."),
            Theorem("card-inflate", "card_inflate", "Size of the inflated carrier",
                Equal(Card(Call("Inflated", K)), Seq(Card(V), Sp, Plus, Sp,
                    new Formula.Subscript(Sum, new Formula.Relation(P, FormulaRelationOperator.MemberOf, V)), Sp,
                    Apply(K, P))),
                "The sum carrier adds one fresh finite leaf fibre per old vertex."),
            Theorem("leaf-positive", "leaf_pos_of_terminal", "An original leaf over a pruned terminal",
                Binder(Forall, "hr", RootPremise(T), All("p", Call("Core", T),
                    Imp(new Formula.Not(Call("Internal", Call("prune", T, Hr), P)),
                        Less(D(0), Card(Call("LeafFibre", T, P)))))),
                "A child exists in the original tree because p is internal there. If that child were itself internal, it would survive pruning and contradict terminality."))));

    private static Formula Roots(Formula body) =>
        Binder(Forall, "hr", RootPremise(T), Binder(Forall, "hs", RootPremise(S), Parenthesized(body)));
    private static Formula RootPremise(Formula tree) => Call("Internal", tree, Call("root", tree));
    private static Formula Binder(Formula symbol, string name, Formula type, Formula body) =>
        Seq(symbol, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Subtype(string variable, Formula carrier, Formula condition) =>
        Seq(OpenBrace, F.Id(variable), Colon, Sp, carrier, Sp, Mid, Sp, condition, CloseBrace);
    private static Formula HasType(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Pair(Formula left, Formula right) => Seq(Langle, Sp, left, Comma, Sp, right, Rangle);
    private static Formula Card(Formula type) => Call("card", type);
    private static Formula Value(Formula member) => Seq(member, Dot, F.Id("val"));
    private static Formula Image(Formula iso, Formula vertex) =>
        Apply(Seq(iso, Dot, F.Id("equiv")), vertex);
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula EquivOf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equivalent, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);

    private static DocumentBlock Definition(string id, string name, string title, Formula formula, string prose) =>
        Node(id, name, title, formula, prose, DescribeRole.Definition);
    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string prose) =>
        Node(id, name, title, formula, prose, DescribeRole.Theorem);
    private static Formula Parameter(string name, Formula type) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type));
    private static Formula Finite(Formula carrier) =>
        Seq(OpenBracket, Call("Fintype", carrier), CloseBracket);
    private static Formula For(Formula body, params Formula[] parameters) =>
        Seq(Forall, Sp, Seq(parameters.Select(parameter => Seq(parameter, Sp)).ToArray()), Comma, Sp,
            Parenthesized(body));

    private static Formula Scope(string name, Formula body)
    {
        var carrier = Parameter("V", F.Id("Type"));
        var tree = Parameter("T", Call("Tree", V));
        var p = Parameter("p", Call("Core", T));
        var counts = Parameter("k", new Formula.TypeArrow(V, Seq(Mathbb, Grp(F.Id("N")))));
        var w = F.Id("W");
        return name switch
        {
            "Core" => For(body, carrier, tree),
            "LeafFibre" => For(body, carrier, tree, p),
            "instFintypeLeafFibre" => For(body, carrier, Finite(V), tree, p),
            "extendIso" or "iso_iff_fibres" => For(body, carrier, Parameter("W", F.Id("Type")),
                Finite(V), Finite(w), tree, Parameter("S", Call("Tree", w))),
            "Inflated" => For(body, carrier, counts),
            "card_inflate" => For(body, carrier, Finite(V), counts),
            "leaf_pos_of_terminal" => For(body, carrier, Finite(V), tree),
            _ => For(body, carrier, tree, counts)
        };
    }

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("leaf-decoration-" + id), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(Scope(name, formula))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
