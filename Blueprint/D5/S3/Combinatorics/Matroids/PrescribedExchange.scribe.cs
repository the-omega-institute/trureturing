using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PrescribedExchangeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PrescribedExchange";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescriptions in opposite base differences extend to one simultaneous exchange bounded by their union rank.",
        H("Rank-bounded simultaneous prescribed exchange"),
        Blocks(Describe.Lean(
            DescribeId.Create("rank-bounded-prescribed-exchange"),
            DeclarationHandle.Create(Module + ".exists_prescribed_exchange"),
            H("Prescribed exchange for arbitrary finite native matroids"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/okischwarcz2025multipleexchange")),
            Blocks(
                Paragraph(Text(
                    "Let E be a finite type in an arbitrary universe, M a native matroid on E, "
                    + "and A and B bases of M. For each prescribed subset X of A minus B and "
                    + "each prescribed subset Y of B minus A, one pair U,V extends both "
                    + "prescriptions inside the respective base differences. The two sets have "
                    + "equal cardinality, bounded by the native rank of X union Y. Removing U "
                    + "from A and adding V gives a base, and removing V from B and adding U "
                    + "also gives a base. Both base conclusions hold for this same pair.")),
                Paragraph(Text(
                    "Cardinality is Set.ncard and rank is ENat.toNat of Matroid.eRk. Finiteness "
                    + "of the ambient type makes these ranks finite. Empty carriers, proper or "
                    + "empty native grounds, empty prescriptions, rank zero, intersecting or "
                    + "coincident bases, loops, coloops and nonrepresentable matroids are included. "
                    + "The statement is an existence theorem and asserts no algorithmic complexity.")),
                Paragraph(Text(
                    "Contract the intersection of the bases and restrict to their union minus "
                    + "that intersection. The resulting bases partition the resulting native "
                    + "ground. Contract X and delete Y in this matroid and in its dual. The "
                    + "base A minus X is common to these two residual minors. Integral weight "
                    + "splitting for the indicator of A minus X produces a single common base C "
                    + "and integral summands c,d for which C is separately minimum in both minors.")),
                Paragraph(Text(
                    "For each integer threshold t, let S(t) contain residual elements with "
                    + "c-weight at most t, and let H(t) be the union of A intersect S(t) and "
                    + "B intersect S(t-1). Integrality and the indicator split identify the "
                    + "complement of H(t) with the d-threshold at minus t. Minimum-base "
                    + "threshold saturation therefore supplies both coupled rank profiles. "
                    + "Two applications of submodularity, together with independence inside "
                    + "A and B, bound the rank increase from S(t-1) to S(t) by the increase "
                    + "in the cardinality of B intersect C intersect S(t).")),
                Paragraph(Text(
                    "Finite lower and upper bounds on the c-weights allow the paired inequality "
                    + "to telescope from the empty threshold to the whole residual ground, "
                    + "including an empty residual ground. The resulting inequality bounds "
                    + "the cardinality of A intersect C plus the cardinality of X by the rank "
                    + "of X union Y. Take U to be the union of A intersect C with X and take "
                    + "V to be B minus C. The common residual base gives both exchanged bases "
                    + "and equal exchange cardinalities. Lifting through restriction and "
                    + "contraction gives both original bases; contraction rank monotonicity "
                    + "gives the stated bound in the original matroid.")),
                Paragraph(Text(
                    "This is the existence assertion of Oki and Schwarcz, Theorem 1.6(i). "
                    + "The rank argument is the paired threshold form of Section 3.1. "
                    + "Theorem 1.6(ii), concerning independence-oracle queries, is a separate assertion."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula e = F.Id("E"), m = F.Id("M"), a = F.Id("A"), b = F.Id("B");
        Formula x = F.Id("X"), y = F.Id("Y"), u = F.Id("U"), v = F.Id("V");
        Formula set = Call("Set", e);
        Formula diff(Formula s, Formula t) => Qualified("Set", "diff", s, t);
        Formula union(Formula s, Formula t) => Qualified("Set", "union", s, t);
        Formula card(Formula s) => Qualified("Set", "ncard", s);
        Formula basis(Formula s) => Qualified("Matroid", "IsBase", m, s);
        Formula subset(Formula s, Formula t) =>
            new Formula.Relation(s, FormulaRelationOperator.SubsetOf, t);
        Formula rank = Qualified("ENat", "toNat", Qualified("Matroid", "eRk", m, union(x, y)));
        Formula conclusion = And(subset(u, diff(a, b)), And(subset(v, diff(b, a)),
            And(subset(x, u), And(subset(y, v),
            And(Equal(card(u), card(v)), And(Leq(card(u), rank),
            And(basis(union(diff(a, u), v)), basis(union(diff(b, v), u)))))))));
        Formula body = Some("U", set, Some("V", set, conclusion));
        body = Imp(basis(a), Imp(basis(b),
            Imp(subset(x, diff(a, b)), Imp(subset(y, diff(b, a)), body))));
        body = All("A", set, All("B", set, All("X", set, All("Y", set, body))));
        body = All("M", Call("Matroid", e), body);
        return Disp(All("E", new Formula.Subscript(F.Id("Type"), F.Id("u")),
            Seq(OpenBracket, Call("Finite", e), CloseBracket, Comma, Sp, body)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot,
            Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp,
            Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp,
            Parenthesized(body));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
