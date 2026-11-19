using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class C128ZeroExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full matrix zero-extension ideal on the compact unit interval.", H("Zero Extension of Whole Matrix C0 Fields"),
        Blocks(Describe.Lean(DescribeId.Create("c128zeroextension"),
            DeclarationHandle.Create("D5/S3/ContinuousObservables/C128ZeroExtension.whole_zero_extension"),
            H("Whole zero extension and inverse restriction"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Y is the closed real interval [0,1]. U is (0,1/4) with every reciprocal 1/n removed for natural n at least 5. M is CStarMatrix (Fin 2) (Fin 2) C with its operator norm. A is the entire algebra C0(U,M), and J is independently defined as all continuous M-valued fields on Y that vanish off U. Ext is extension by zero, Res is restriction, and inc is the original inclusion U into Y.")),
                Paragraph(Text("The complex linear map extensionHom preserves multiplication and star. It is an isometry onto all of J. The ideal J is closed, is closed under right multiplication by every ambient continuous field, and is star invariant; left multiplication is part of its Ideal structure. For every g in J, Ext(Res(g))=g; every f in A is recovered pointwise on U. All norms are the inherited matrix operator uniform norms.")),
                Paragraph(Text("The collapse of the complement of U to the added point of OnePoint U is continuous: open neighborhoods of that point have compact complement in U, whose image is closed in the real line. Composing this collapse with the existing OnePoint extension proves continuity at every endpoint and deleted reciprocal. Conversely, every positive norm-level set of a field in J is compact in Y and lies wholly in U. Pulling these level sets back proves that its restriction vanishes at infinity. No compact-support condition is imposed on a field in A.")),
                Paragraph(Text("The selfadjoint restriction uses this whole ideal. This result supplies no polynomial-domain completeness, multiplier reconstruction, norm recovery on original polynomial labels, complete quantum model, or physical realization."))),
            DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] clauses) => Seq(clauses.SelectMany((c, i) =>
        i == 0 ? new Formula[] { Par(c) } : new Formula[] { Sp, Land, Sp, Par(c) }).ToArray());
    private static Formula Statement() =>
        And(
            Call("Isometry", V("extensionHom")),
            Seq(Call("range", V("extensionHom")), Eq, V("J")),
            Call("IsClosed", V("J")),
            All("g", V("J"), Seq(Call("Ext", Call("Res", V("g"))), Eq, V("g"))),
            All("f", V("A"), All("t", V("U"), Seq(Call("Ext", V("f"), Call("inc", V("t"))), Eq, Call("f", V("t"))))),
            All("g", Call("ContinuousMap", V("Y"), V("M")), Seq(
                V("g"), InMacro, Sp, V("J"), Sp, Rightarrow, Sp,
                All("h", Call("ContinuousMap", V("Y"), V("M")), And(
                    Seq(V("g"), V("h"), InMacro, Sp, V("J")),
                    Seq(Call("star", V("g")), InMacro, Sp, V("J")))))));
}
