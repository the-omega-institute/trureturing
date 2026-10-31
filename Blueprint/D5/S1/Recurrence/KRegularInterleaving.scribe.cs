using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class KRegularInterleavingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/shallit2020merge");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite interleaving of integer-valued k-regular residue streams is k-regular.",
        H("Finite interleavings of integer k-regular sequences"),
        Blocks(
            Paragraph(Text(
                "A sequence has domain the natural numbers, including zero, and values in the integers. "
                + "Its full k-kernel K_k(s) consists of all sequences n ↦ s(k^e n+c), for natural e and c "
                + "with c<k^e. Write Regular(k,s) when the integer span of this entire kernel is finitely "
                + "generated. The values and the kernel may both be infinite.")),
            Paragraph(Text("Affine-subsequence closure is supplied by "),
                Ref("D5/S1/Recurrence/KRegularAffineSubsequence.is_k_regular_affine_subsequence"),
                Text("; its literature statement is recorded in "),
                Ref("D5/L/RecurrenceComposition/alloucheshallit1992regular"), Text(".")),
            Describe.Lean(DescribeId.Create("k-regular-interleaving-closure"),
                DeclarationHandle.Create("D5/S1/Recurrence/KRegularInterleaving.is_k_regular_interleaving"),
                H("Interleaving closure"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural base k≥2, every natural interleaving width a≥1, and every "
                        + "integer-valued sequence s, assume that n ↦ s(an+i) is k-regular for every "
                        + "natural i<a. Then s is k-regular in that same base. This is the integer-coefficient "
                        + "case of the cited Theorem 1. The width need not be coprime to the base. No "
                        + "finite-range, finite-kernel, automaticity, periodicity, recurrence, common "
                        + "generating-family, or regularity assumption on s occurs among the hypotheses.")),
                    Paragraph(Text(
                        "For N and r natural, let E(N,r)h(n) equal h(⌊n/N⌋) when n mod N=r and zero "
                        + "otherwise. This is an integer-linear insertion map. Put f_i(m)=s(am+i) and "
                        + "T_i=E(a,i)f_i, so s is the finite sum of the T_i for 0≤i<a.")),
                    Paragraph(Text(
                        "Fix one input f_i. The attained values g=gcd(k^e,a) form a finite set, since "
                        + "1≤g≤a. For each such g, choose the least exponent t_g attaining it. Set "
                        + "u_g=k^(t_g)/g and N_g=a/g. Both are positive. For every exponent e attaining g, "
                        + "minimality gives t_g≤e and k^e/g=k^(e−t_g)u_g. For each d<u_g, use affine-subsequence "
                        + "closure to obtain the finitely generated span H(g,d) of the k-kernel of "
                        + "n ↦ f_i(u_g n+d). Form the single finite sum W_i of E(N_g,r)(H(g,d)) over all "
                        + "attained g, d<u_g, and r<N_g. Linear images and finite sums preserve finite generation.")),
                    Paragraph(Text(
                        "To contain the whole kernel, take arbitrary e and c<k^e. With K=k^e and "
                        + "g=gcd(K,a), either the mask is never active and T_i(Kn+c) vanishes for every n, or the mask is active on exactly one residue "
                        + "class r modulo N_g. Indeed, canceling K in a congruence modulo a divides the "
                        + "modulus by gcd(K,a). Choose the least nonnegative representative r<N_g of an "
                        + "index satisfying Kn+c ≡ i modulo a. Then Kr+c=am_0+i with m_0<K/g, and for every n the "
                        + "masked sample is exactly E(N_g,r) applied to ℓ ↦ f_i((K/g)ℓ+m_0). Write "
                        + "m_0=u_g q+d by Euclidean division. The strict bound is q<k^(e−t_g), while d<u_g. "
                        + "Thus this inner sequence is a genuine member of the k-kernel of "
                        + "n ↦ f_i(u_g n+d), and its insertion lies in W_i. The same W_i works for every "
                        + "e and c, including e=c=0 and m_0=0.")),
                    Paragraph(Text(
                        "Consequently the entire kernel span of each T_i is contained in its finitely "
                        + "generated W_i. "
                        + "The full kernel of s lies in the same finite sum of the W_i, "
                        + "which is finitely generated. The integer span of K_k(s) is therefore finitely generated because the integers are Noetherian. The construction "
                        + "also includes a=1 and N_g=1. It concerns integer coefficients and supplies no "
                        + "general coefficient-ring theorem or finite-state transducer construction."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var k = F.Id("k");
        var a = F.Id("a");
        var s = F.Id("s");
        var i = F.Id("i");
        var n = F.Id("n");
        var index = new Formula.Binary(new Formula.Binary(a, FormulaBinaryOperator.Multiply, n),
            FormulaBinaryOperator.Add, i);
        var observed = Seq(Open, n, Colon, Sp, Naturals(), Sp, Mapsto, Sp, Call("s", index), Close);
        var residues = All("i", Naturals(), Implies(Less(i, a), Call("Regular", k, observed)));
        return Disp(All("k", Naturals(), All("a", Naturals(), All("s", SequenceType(),
            Implies(Le(D(2), k), Implies(Le(D(1), a),
                Implies(residues, Call("Regular", k, s))))))));
    }

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula SequenceType() => Seq(Open, Naturals(), Sp, To, Sp, new Formula.Integers(), Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
}
