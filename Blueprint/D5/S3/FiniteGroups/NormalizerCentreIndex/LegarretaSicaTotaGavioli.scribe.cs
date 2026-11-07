using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NormalizerCentreIndex;

internal sealed class LegarretaSicaTotaGavioliDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/legarreta2010normalizers");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centre index is unbounded while the number of normalizer classes stays eight.",
        H("Normalizer counts and centre index"), Blocks(
            Describe.Lean(DescribeId.Create("normalizer-centre-index-question"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.claim"),
                H("The general-group question"), StatementSource.FromAuthor(Disp(Eqn(X("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Question 3.3. Let G be a group satisfying the normalizer condition, and suppose that ω(G) is finite. If s(G) > ω(G), is |G : Z(G)| ω(G)-bounded? Is this true at least for finite p-groups?" +
                    " Printed page 1174. “NC: every proper subgroup H of G is properly contained in its normalizer N_G(H).” Printed page 1169. The target is the first question. The function B maps natural numbers to natural numbers. " +
                    "NormalizerWitness counts distinct normalizer subgroups, including the whole group; NormalizerClass identifies them by inner conjugacy. " +
                    "The centre index and the number of normalizers are cardinal-valued. The cardinal comparison retains infinite indices. " +
                    "omega is Nat.card of the quotient, used with its explicit finiteness hypothesis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalizer-centre-index-refutation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.result"),
                H("A family with fixed normalizer counts"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each odd prime p, take the product of the group of order sixteen with presentation " +
                    "a⁸ = b² = 1, b⁻¹ab = a³, and the modular group of order p³ with action yxy⁻¹ = x¹⁺ᵖ. " +
                    "The first factor has five normalizers and four conjugacy classes of normalizers. The modular factor has two of each. " +
                    "Coprimality splits subgroups and normalizers coordinatewise. The product has ten normalizers, eight classes, " +
                    "and centre index 8p². It is finite nilpotent, so every proper subgroup is strictly contained in its normalizer. " +
                    "Unbounded odd primes contradict any natural bound at eight. The separate finite-p-group question is left open."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        var g = X("G"); var h = X("H"); var b = X("B");
        var normalizer = App(Q("Subgroup", "normalizer"), Cast(h, Call("Set", g)));
        var nc = All("H", Call("Subgroup", g), Imp(Seq(h, Neq, Sp, Q("Top", "top")), Seq(h, Lt, normalizer)));
        return Ex("B", new Formula.TypeArrow(Nat(), Nat()), Gforall(
            Imp(nc, Imp(Call("Finite", Call("NormalizerClass", g)),
                Imp(Seq(Cast(Cast(Call("omega", g), Nat()), X("Cardinal")), Lt, Call("sCard", g)),
                    Seq(Call("centreIndex", g), Le, Sp, Cast(Cast(App(b, Call("omega", g)), Nat()), X("Cardinal"))))))));
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(X(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Gforall(Formula body) => All("G", X("Type"), Instance(Call("Group", X("G")), body));
}
