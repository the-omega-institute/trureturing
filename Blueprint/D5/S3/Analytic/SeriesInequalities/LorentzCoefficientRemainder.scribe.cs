using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class LorentzCoefficientRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Lorentz remainder is uniformly small in the original Bernstein coefficient norm.",
        H("The Low-Degree Lorentz Coefficient Remainder"),
        Blocks(
            Paragraph(Text("Write B(d,c) for the polynomial with original normalized degree-d "
                + "Bernstein array c, and Q(m,r,P) for the Lorentz operator evaluated on the "
                + "actual iterated derivatives of P at i/m. Its correction polynomials are the "
                + "inverse convolution of the binomial central moments. Array norms are maximum "
                + "coefficient moduli, and degree elevation is included in the polynomial identity.")),
            Entry("reproduction", "lorentz_reproduction", "Exact polynomial reproduction",
                ReproductionFormula(), true,
                "Every complex polynomial of degree at most r is reproduced for each positive "
                + "grid size m. Finite Taylor expansion and the defining convolution identity "
                + "cancel the nonconstant centered terms. This is the complex-scalar form of "
                + "Lemma 14 of Holtz, Nazarov and Peres."),
            Entry("coefficient-remainder", "low_degree_coefficient_remainder", "A uniform bound for every original array",
                RemainderFormula(), false,
                "For every natural r, one constant K at least one works simultaneously for all "
                + "m at least d at least one and every original complex coefficient array c. "
                + "The remainder is represented at degree m+r by one array a, and the estimate "
                + "holds for its full maximum norm. If d is at most r, this entire array is zero. "
                + "No derivative hypothesis, selected input array, or quadratic separation of "
                + "m from d is imposed."),
            Paragraph(Text("The proof combines a local Taylor remainder with the effective "
                + "Lorentz coefficient kernel. The large-ratio regime uses the centered "
                + "Taylor coefficient estimate; a stability bound handles the complementary "
                + "regime. Bernstein reconstruction supplies the same coefficient array for "
                + "all output indices. This establishes the polynomial coefficient remainder "
                + "and does not assert later smooth-function continuation or probabilistic "
                + "factory constructions.")))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, bool literature, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(I(name), [.. args]);
    private static Formula Field(string name) => Seq(Mathbb, Grp(I(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula n) => Seq(Call("Fin",Seq(n,Plus,D(1))),To,Sp,Field("C"));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Par(Formula x) => Seq(Open,x,Close);

    private static Formula ReproductionFormula()
    {
        Formula m=I("m"), r=I("r"), p=I("P");
        return Disp(All("m",Field("N"),All("r",Field("N"),All("P",Call("Polynomial",Field("C")),
            Seq(D(0),Lt,Sp,m,Land,Sp,Call("natDegree",p),Le,Sp,r,Rightarrow,Sp,Call("Q",m,r,p),Eq,p)))));
    }

    private static Formula RemainderFormula()
    {
        Formula r=I("r"), k=I("K"), d=I("d"), m=I("m"), c=I("c"), a=I("a");
        Formula p=Call("B",d,c), degree=Seq(m,Plus,r);
        Formula body=Ex("a",Arr(degree),Seq(p,Minus,Call("Q",m,r,p),Eq,Call("B",degree,a),Land,Sp,
            Norm(a),Le,Sp,k,Cdot, Sp,Pow(Fr(d,m),Fr(Seq(r,Plus,D(1)),D(2))),Cdot, Sp,Norm(c),Land,Sp,
            Par(Seq(d,Le,Sp,r,Rightarrow,Sp,a,Eq,D(0)))));
        body=All("c",Arr(d),body);
        body=All("d",Field("N"),All("m",Field("N"),Seq(D(0),Lt,Sp,d,Land,Sp,d,Le,Sp,m,Rightarrow,Sp,body)));
        return Disp(All("r",Field("N"),Ex("K",Field("R"),Seq(D(1),Le,Sp,k,Land,Sp,body))));
    }
}
