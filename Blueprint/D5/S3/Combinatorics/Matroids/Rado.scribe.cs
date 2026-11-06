using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RadoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank inequalities characterize independent representatives of a finite indexed family.",
        H("Rado's independent-transversal criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("rado-independent-transversal"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/Rado.rado_independent_transversal"),
            H("Independent representatives and subfamily rank"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/rado1942independence")),
            Blocks(
                Paragraph(Text("Let I : Type u and E : Type v be finite types in independent universes. For any native matroid M on E and any family A : I -> Set E, an independent transversal is one function f : I -> E that is injective, satisfies f i in A i for every i, and has M-independent range. Such a function exists if and only if, for every finite subfamily J : Finset I, the cardinality of J, coerced to ENat, is at most the rank of the union of A i over i in J. The same M and A occur on both sides of the equivalence.")),
                Paragraph(Text("The ground M.E is arbitrary, and the sets A i need not lie in it. Independence forces the selected representatives into the ground. The assumptions are only Finite I and Finite E; Fintype and decidable equality are chosen internally. Empty index and carrier types, loops and rank zero are included. No nonemptiness, full-ground, positive-rank, field or representability premise is required.")),
                Paragraph(Text("Necessity restricts the selected independent range to each subfamily. Injectivity identifies its cardinality with that subfamily's cardinality, and rank monotonicity gives the inequality. Sufficiency uses strong induction on the family size. A nonempty proper tight subfamily supplies a basis of its union; contract its representatives, solve the complementary family, and glue the two independent selections. If every nonempty proper subfamily has strict slack, choose a nonloop for one index, contract it, solve the remaining indices, and adjoin that representative. The empty family starts the induction.")),
                Paragraph(Text("Contraction uses the native identity (M / C).eRk Y + M.eRk C = M.eRk (Y union C). For an independent C its rank equals its cardinality. Finite ENat cancellation gives the two rank estimates needed in the tight and strict branches. Independence after contraction keeps the new representatives disjoint from C, so the glued function is injective and its whole range is independent."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var range = A(Q("Set", "range"), V("f"));
        var membership = All("i", V("I"), Member(A(V("f"), V("i")), A(V("A"), V("i"))));
        var transversal = Some("f", Arrow(V("I"), V("E")),
            And(A(Q("Function", "Injective"), V("f")),
                And(membership, A(Q("Matroid", "Indep"), V("M"), range))));
        var union = A(Q("Set", "iUnion"), Lam("i", V("I"),
            A(Q("Set", "iUnion"), Lam("h", Member(V("i"), V("J")), A(V("A"), V("i")))));
        var castCard = A(Q("Nat", "cast"), A(Q("Finset", "card"), V("J")));
        var inequalities = All("J", A(V("Finset"), V("I")),
            new Formula.Relation(castCard, FormulaRelationOperator.LessThanOrEqual,
                A(Q("Matroid", "eRk"), V("M"), union)));
        Formula result = new Formula.Logic(Parenthesized(transversal), FormulaLogicOperator.Iff,
            Parenthesized(inequalities));
        result = All("A", Arrow(V("I"), A(V("Set"), V("E"))), result);
        result = All("M", A(V("Matroid"), V("E")), result);
        result = Inst(A(V("Finite"), V("E")), result);
        result = Inst(A(V("Finite"), V("I")), result);
        result = All("E", new Formula.Subscript(V("Type"), V("v")), result);
        return All("I", new Formula.Subscript(V("Type"), V("u")), result);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula A(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Member(Formula x, Formula set) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, set);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
