using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class NonconformalCliqueObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite nonconformal clique yields finite nonempty relations whose complete "
            + "pairwise projections agree, although no global tuple realizes them.",
        H("Nonconformal Clique Obstruction"),
        Blocks(
            Paragraph(Text(
                "E is an arbitrary scope index type, V is a finite variable type, S(e) is a "
                    + "subset of V, and C is a finite subset of V with at least three elements. "
                    + "Every pair of distinct variables in C occurs together in some scope, "
                    + "but no scope contains C. Put q = card(C) - 1. An assignment on a scope U "
                    + "is a function from the subtype U to Fin(q). Empty, repeated, and nested "
                    + "scopes, variables outside C, and variables outside all scopes are allowed.")),
            Describe.Lean(DescribeId.Create("injectivity-on-clique"),
                DeclarationHandle.Create(Module + "InjectiveOnClique"),
                H("Only clique coordinates are constrained"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("InjectiveOnClique", F.Id("C"), F.Id("U"), F.Id("q"), F.Id("r")),
                    Sp, Iff, Sp,
                    Call("Injective", Call("restrict", F.Id("r"),
                        Call("intersection", F.Id("U"), F.Id("C"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The predicate requires injectivity of the scope tuple restricted to U "
                        + "intersect C. It imposes no condition on any coordinate outside C."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-injective-clique-relation"),
                DeclarationHandle.Create(Module + "cliqueRows"),
                H("The full finite relation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("cliqueRows", F.Id("C"), F.Id("U"), F.Id("q")), Sp, Eq, Sp,
                    OpenBrace, F.Id("r"), Colon, Sp, F.Id("U"), Sp, To, Sp,
                    Call("Fin", F.Id("q")), Sp, Mid, Sp,
                    Call("InjectiveOnClique", F.Id("C"), F.Id("U"), F.Id("q"), F.Id("r")),
                    CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The defining set is converted to a finset using finiteness of V and "
                        + "Fin(q). Every tuple satisfying the injectivity condition is included; "
                        + "values outside C are unrestricted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonconformal-clique-obstruction"),
                DeclarationHandle.Create(Module + "nonconformal_clique_obstruction"),
                H("Complete pairwise consistency without a global tuple"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each scope choose the relation R(e) = cliqueRows(C,S(e),q). "
                            + "Noncontainment gives a clique variable missing from S(e), so "
                            + "card(S(e) intersect C) is at most q. The upstream embedding "
                            + "theorem Function.Embedding.nonempty_of_card_le supplies a finite "
                            + "injection into Fin(q), yielding a local tuple.")),
                    Paragraph(Text(
                        "For an arbitrary admissible tuple on S(e), start with such an injection "
                            + "on S(f) intersect C. Equiv.Perm.exists_extending_pair permutes its "
                            + "colors to agree with all prescribed values on S(e) intersect S(f) "
                            + "intersect C. On overlap coordinates outside C copy the original "
                            + "tuple exactly; choose a default color only on remaining coordinates "
                            + "outside C. This constructs a tuple in R(f) with the same complete "
                            + "overlap restriction. Applying the construction in both directions "
                            + "proves equality of the complete projection images.")),
                    Paragraph(Text(
                        "If a global tuple restricted into every R(e), any distinct x,y in C "
                            + "would occur together in some scope and hence have different values. "
                            + "Thus the global tuple would inject C into Fin(card(C)-1), contrary "
                            + "to Fintype.card_le_of_injective.")),
                    Paragraph(Text(
                        "For this specific relation construction the color threshold is sharp: "
                            + "with card(C) colors, inject C into Fin(card(C)) and extend the "
                            + "assignment to V using a default color outside C. Every scope "
                            + "restriction belongs to its full injective-clique relation.")),
                    Paragraph(Text(
                        "This is a known-result formalization in the classical theory of acyclic "
                            + "database schemes, not a novelty claim: Beeri, Fagin, Maier, and "
                            + "Yannakakis, On the Desirability of Acyclic Database Schemes, Journal "
                            + "of the ACM 30(3), 1983, DOI 10.1145/2402.322389. The Lean proof "
                            + "supplies the indexed-scope and finite-alphabet construction explicitly. "
                            + "It treats only the nonconformal branch; the full classification "
                            + "in issue #30141 remains unresolved."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula q = Seq(Call("card", F.Id("C")), Sp, Minus, Sp, D(1));
        Formula colors = Call("Fin", q);
        Formula scope = Call("S", F.Id("e"));
        Formula pairCondition = Seq(
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Sp, InMacro, Sp, F.Id("C"),
            Comma, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("y"), Sp, To, Sp,
            Exists, Sp, F.Id("e"), Colon, Sp, F.Id("E"), Comma, Sp,
            F.Id("x"), Sp, InMacro, Sp, scope, Sp, Land, Sp,
            F.Id("y"), Sp, InMacro, Sp, scope);
        Formula properCondition = Seq(
            Forall, Sp, F.Id("e"), Colon, Sp, F.Id("E"), Comma, Sp, Neg,
            Call("Subset", F.Id("C"), scope));
        Formula overlap = Call("intersection", Call("S", F.Id("e")), Call("S", F.Id("f")));
        Formula projections = Seq(
            Forall, Sp, F.Id("e"), Comma, Sp, F.Id("f"), Colon, Sp, F.Id("E"), Comma, Sp,
            Call("image", Call("restrict", overlap), Call("R", F.Id("e"))), Sp, Eq, Sp,
            Call("image", Call("restrict", overlap), Call("R", F.Id("f"))));
        Formula noGlobal = Seq(
            Neg, Exists, Sp, F.Id("g"), Colon, Sp, F.Id("V"), Sp, To, Sp, colors, Comma, Sp,
            Forall, Sp, F.Id("e"), Colon, Sp, F.Id("E"), Comma, Sp,
            Call("restrict", F.Id("g"), scope), Sp, InMacro, Sp, Call("R", F.Id("e")));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("E"), Comma, Sp, F.Id("V"), Comma, Sp,
            Call("Finite", F.Id("V")), Comma, Sp,
            Forall, Sp, F.Id("S"), Colon, Sp, F.Id("E"), Sp, To, Sp, Call("Set", F.Id("V")),
            Comma, Sp, F.Id("C"), Colon, Sp, Call("Finset", F.Id("V")), Comma,
            RowBreak, Grp(),
            Open, D(3), Sp, Leq, Sp, Call("card", F.Id("C")), Sp, Land, Sp,
            Open, pairCondition, Close, Sp, Land, Sp, Open, properCondition, Close, Close,
            Sp, To, RowBreak, Grp(),
            Exists, Sp, F.Id("R"), Colon, Sp,
            Seq(Open, F.Id("e"), Colon, Sp, F.Id("E"), Close, Sp, To, Sp,
                Call("Finset", Seq(scope, Sp, To, Sp, colors))),
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, F.Id("e"), Colon, Sp, F.Id("E"), Comma, Sp,
            Call("Nonempty", Call("R", F.Id("e"))), Close, Sp, Land, RowBreak, Grp(),
            Open, projections, Close, Sp, Land, RowBreak, Grp(),
            Open, noGlobal, Close,
            End, Grp(F.Id("gathered"))));
    }
}
