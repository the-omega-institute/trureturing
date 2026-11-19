using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks;
internal sealed class HardinA229585StripOrbit5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit5.";
    private const string Note = "D5/L/SpinModels/hardin2013a229585";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.")),
            Describe.Lean(DescribeId.Create("canonical-next"),
                DeclarationHandle.Create(Prefix + "canonical_next"), H("Successor multiset on a class interval"),
                StatementSource.FromAuthor(Disp(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229585StripData.Valid", V("p"), Call("Fin.val", V("d"))), Imp(Call("HardinA233177Canonical.Canonical", V("p")), Imp(And(Leq(Num("40"), Call("Fin.val", Call("HardinA229585StripData.cl", V("p"), Call("Fin.val", V("d"))))), Lt(Call("Fin.val", Call("HardinA229585StripData.cl", V("p"), Call("Fin.val", V("d")))), Num("48"))), Eq(Call("HardinA229585StripOrbit.nextClasses", V("p"), Call("Fin.val", V("d"))), Call("HardinA229585StripOrbit.images", Call("HardinA229585StripData.cl", V("p"), Call("Fin.val", V("d")))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("All canonical boundaries in this interval are checked with their exact residual budget."))), DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));

}
