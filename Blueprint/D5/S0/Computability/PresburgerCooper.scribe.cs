using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerCooperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive period reduces integer existence with bounds to finite residue tests.", H("Periodic integer predicates and finite residues"),
        Blocks(Paragraph(Text("P is an arbitrary predicate on integers; no decision procedure for P is assumed in these arithmetic theorems. The period m is a positive natural number, and P(x+m) iff P(x) holds for every integer x. periodic_shift_of_mod extends this law to every integer multiple of m, using positive and negative induction.")),
            Paragraph(Text("periodic_interval states that a P-point in [lo,hi] exists exactly when some k<m satisfies lo+k<=hi and P(lo+k). Division with remainder moves a point down into the first period after lo, preserving P and the upper bound. periodic_has_residue instead moves a point into [0,m). A nonempty residue can be shifted above every finite list of lower bounds or below every finite list of upper bounds.")),
            Paragraph(Text("Here members(los) and members(his) mean list membership, and cast embeds naturals into integers. maxFrom and minFrom retain the starting integer as well as the list; their comparison and membership lemmas let the proof choose an extremal endpoint. The finite criterion combines these facts, including empty bound lists.")),
            Describe.Lean(DescribeId.Create("cooper-finite-criterion"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerCooper.cooper_finite_criterion"),
            H("One-sided and two-sided finite criterion"), StatementSource.FromAuthor(F.Disp(A("P", F.Seq(V("Int"), F.Sp, F.To, F.Sp, V("Prop")), A("m", V("Nat"), R(T(Num(0),V("m")), R(A("x", V("Int"), I(Call("P", Add(V("x"), Call("cast", V("m")))), Call("P", V("x")))), A("los", Call("List", V("Int")), A("his", Call("List", V("Int")), I(X("x", V("Int"), C(A("l", Call("members", V("los")), L(V("l"), V("x"))), C(A("h", Call("members", V("his")), L(V("x"), V("h"))), Call("P", V("x"))))), Call("if", Call("or",Call("isEmpty",V("los")),Call("isEmpty",V("his"))), X("k", V("Nat"), C(T(V("k"), V("m")), Call("P", Call("cast", V("k"))))), A("l", Call("members", V("los")), A("h", Call("members", V("his")), X("k", V("Nat"), C(T(V("k"),V("m")), C(L(Add(V("l"), Call("cast", V("k"))),V("h")), Call("P", Add(V("l"), Call("cast", V("k"))))))))))))))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("If either bound list is empty, it suffices to check one full set of residues. Otherwise each lower/upper pair must admit a residue-offset point. For the reverse implication, take the greatest lower bound and least upper bound; their pair supplies a common feasible point. This is a semantic reduction, not a complexity estimate."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerSyntax"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula X(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula I(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Iff, F.Sp, F.Open, right, F.Close);
    private static Formula R(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Implies, F.Sp, F.Open, right, F.Close);
    private static Formula C(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Land, F.Sp, F.Open, right, F.Close);
    private static Formula L(Formula left, Formula right) => F.Seq(left, F.Sp, F.Leq, F.Sp, right);
    private static Formula T(Formula left, Formula right) => F.Seq(left, F.Sp, F.Lt, F.Sp, right);
}
