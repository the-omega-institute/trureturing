using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class NormalizerImageActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NormalizerImageAction", H("NormalizerImageAction"), Blocks(
            Paragraph(Text("The representation, image, image automorphisms and center action are constructed from the same operators on the original carrier. Semisimplicity and isotypy refer to the actual restricted group-algebra module. The algebra proof of Skolem-Noether is reused from AxiomMath/Stacks at revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. Neither faithfulness on the center nor an inner implementer is assumed.")),
            Paragraph(Text("Conjugating an actual operator agrees with applying normal-subgroup conjugation to its group-algebra input. The identity follows by group-algebra induction.")),
            Paragraph(Text("An element of the normal subgroup acts on the image by conjugation by its actual representation unit.")),
            Paragraph(Text("The normal subgroup therefore acts trivially on the center.")),
            Paragraph(Text("The simple image center is a field. If an element fixes it, Skolem-Noether supplies an inner implementer in the actual image. The Frobenius inner-action obstruction then forces that element into the normal subgroup. A complement intersects this kernel trivially, giving a faithful action on the actual center.")),
            Paragraph(Text("The notation with actualModule in each of the two module hypotheses installs exactly the representation-induced k[N]-action on U. The group H need not be finite; only N is required finite here. The scalar field, group and carrier universes are independent.")),
            Describe.Lean(DescribeId.Create("normalizerimageaction-complement-center-kernel-eq-bot"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.complement_center_kernel_eq_bot"), H("complement center kernel eq bot"), StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A complement element acting trivially on the actual component center must lie in N and hence must be the identity."))), DescribeRole.Theorem))));

    private static Formula Actual(Formula cls) => Seq(Operatorname, Grp(I("with")), Sp,
        App(Q("NormalizerImageAction", "actualModule"), I("rho"), I("N")), Comma, Sp, cls);
    private static Formula Statement()
    {
        Formula k = I("k"), h = I("H"), u = I("U"), n = I("N"), rho = I("rho"), j = I("J");
        Formula ga = App(I("MonoidAlgebra"), k, n);
        Formula restricted = App(Q("MonoidHom", "comp"), App(Q("NormalizerImageAction", "representation"), rho), App(Q("Subgroup", "subtype"), n));
        Formula act = App(Q("MonoidHom", "comp"), App(Q("NormalizerImageAction", "centerAction"), rho, n), App(Q("Subgroup", "subtype"), j));
        Formula p = Eq(App(Q("MonoidHom", "ker"), act), Q("Bot", "bot"));
        p = All("hJ", App(Seq(Q("Subgroup", "IsComplement"), Apos), n, j), p);
        p = All("J", App(I("Subgroup"), h), p);
        p = All("hnt", Not(App(Q("Representation", "IsTrivial"), restricted)), p);
        Formula free = All("h", h, ImpTo(Not(new Formula.Relation(I("h"), FormulaRelationOperator.MemberOf, n)),
            All("n", n, ImpTo(Eq(App(App(Q("MulAut", "conjNormal"), I("h")), I("n")), I("n")), Eq(I("n"), D(1))))));
        p = All("hfix", free, p);
        p = All("hiso", Actual(App(I("IsIsotypic"), ga, u)), p);
        p = All("hsemi", Actual(App(I("IsSemisimpleModule"), ga, u)), p);
        p = Inst(App(I("Nontrivial"), u), p); p = Inst(App(Q("Module", "Finite"), k, u), p); p = Inst(App(I("Finite"), n), p);
        p = Inst(App(Q("Subgroup", "Normal"), n), p); p = All("N", App(I("Subgroup"), h), p);
        p = All("rho", App(I("MonoidHom"), h, App(I("LinearEquiv"), App(Q("RingHom", "id"), k), u, u)), p);
        p = Inst(App(I("Module"), k, u), p); p = Inst(App(I("AddCommGroup"), u), p);
        p = Inst(App(I("Group"), h), p); p = Inst(App(I("Field"), k), p);
        return All("k", Ty(), All("H", Ty(), All("U", Ty(), p)));
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Not(Formula p) => new Formula.Not(p);
    private static Formula ImpTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);
}
