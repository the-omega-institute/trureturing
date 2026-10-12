using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.WhiteBoxLossFiberLaw;

internal sealed class TwoAtomMatchingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef RadialSource =
        LibraryNoteRef.Create("D5/L/SparseCoding/parikhboyd2014proximal");
    private static readonly LibraryNoteRef MergingSource =
        LibraryNoteRef.Create("D5/L/SparseCoding/mais2026superposition");
    private static Formula Flow(params Formula[] items) => Seq(items.SelectMany(
        (x,j) => j == 0 ? new[]{x} : new[]{Sp,x}).ToArray());
    private static readonly Formula lam = LambdaLower, delta = DeltaLower;
    private static readonly Formula n = F.Id("n"), m = F.Id("m"), e = F.Id("e"),
        u = F.Id("u"), w = F.Id("w"), a = F.Id("a"), b = F.Id("b"),
        c = F.Id("c"), d = F.Id("d"), i = F.Id("i"), t = F.Id("t");
    private static Formula Sub(Formula x, Formula y) => Flow(x, Underscore, Grp(y));
    private static Formula Sq(Formula x) => Flow(x, Caret, Grp(D(2)));
    private static Formula Norm(Formula x) => Flow(Vert, x, Vert);
    private static Formula Call(string name, params Formula[] args) => Flow(
        F.Id(name), Open, Flow(args.SelectMany((x,j) => j == 0 ? new[]{x} : new[]{Comma,x}).ToArray()), Close);
    private static Formula Cost(Formula x) => Call("C", x, F.Id("D"));
    private static Formula Radial(Formula? amplitude = null) => Flow(Open, lam, amplitude ?? n,
        Minus, Frac, Grp(Sq(lam)), Grp(D(2)), Close);
    private static Formula Energy() => Call("E", Flow(n,e), F.Id("D"), c);
    private static Formula Gap(Formula amplitude) => Call("g", amplitude, delta);
    private static Formula Near(Formula atom, Formula target) => Flow(Call("dist",atom,target),Lt,delta);
    private static Formula Match() => Flow(Open,Near(Sub(d,D(0)),u),Land,Near(Sub(d,D(1)),w),Close,
        Lor,Open,Near(Sub(d,D(0)),w),Land,Near(Sub(d,D(1)),u),Close);
    private static Formula ExactMatch() => Flow(Open,Sub(d,D(0)),Eq,u,Land,Sub(d,D(1)),Eq,w,Close,
        Lor,Open,Sub(d,D(0)),Eq,w,Land,Sub(d,D(1)),Eq,u,Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Near-radial nonnegative coding costs force simultaneous dictionary matching.",
        H("Quantitative Two-Atom Matching"),
        Blocks(
            Paragraph(Text("The ambient space is any real inner-product space, including every finite Euclidean space. " +
                "D is an ordered pair of unit vectors; c has two nonnegative real entries. " +
                "C(x,D) is the infimum of norm(x-Dc)^2/2+lambda(c0+c1). " +
                "No independence, distinctness or plane restriction is imposed on the dictionary atoms.")),
            Paragraph(Text("The radial floor lambda norm(x) minus lambda squared over two comes from the Euclidean-norm proximal formula in Parikh and Boyd, Proximal Algorithms, Section 6.5.1. " +
                "The two-atom zero-weight merging result has a precedent in the Positive-penalty merging proposition of the MAIS-A3 research draft, recorded in mais2026superposition; that source is not peer reviewed. " +
                "The formulations here use arbitrary real inner-product spaces and allow the amplitude and regularization ranges stated separately below. " +
                "The quantitative contribution is a simultaneous match for the same dictionary with an explicit positive gap, followed by uniform localization of every small positive-weight minimizer.")),
            Describe.Lean(
                DescribeId.Create("code-energy-excess-eq"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_energy_excess_eq"),
                H("Square completion"),
                StatementSource.FromAuthor(Disp(Flow(Energy(), Minus, Radial(), Eq, Frac, Grp(Sq(Norm(Flow(Open,n,Minus,lam,Close,e,Minus,Flow(F.Id("D"),c))))), Grp(D(2)), Plus, lam, Sum, Underscore, Grp(i), Sub(c,i), Open,D(1),Minus,Langle,e,Comma,Sub(d,i),Rangle,Close))),
                AssessedProvenance.FromRepo(RadialSource),
                Blocks(Paragraph(Text("For any real amplitude n and regularization parameter lambda, any unit direction e, any ordered unit dictionary D and any two-coordinate real code c, the energy excess over lambda n minus lambda squared over two equals the displayed squared residual and correlation-defect sum. No positivity assumption is needed for this identity. This square-completion decomposition exposes the correlation defects behind the classical proximal radial floor and supplies the directional estimates below."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-code-energy-lower-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.feasible_code_energy_lower_bound"),
                H("Pointwise radial lower bound"),
                StatementSource.FromAuthor(Disp(Flow(Radial(),Le,Energy()))),
                AssessedProvenance.FromLiterature(RadialSource),
                Blocks(Paragraph(Text("For every real amplitude n, unit direction e, ordered unit dictionary D, nonnegative lambda and coordinatewise nonnegative code c, the radial baseline is at most the code energy. Each directional defect is nonnegative by Cauchy-Schwarz. The known core is the radial inequality underlying Parikh and Boyd's proximal formula; its pointwise form here also allows arbitrary real amplitudes, lambda=0 and any real inner-product space."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("code-cost-radial-lower-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_radial_lower_bound"),
                H("Infimal radial lower bound"),
                StatementSource.FromAuthor(Disp(Flow(Radial(),Le,Cost(Flow(n,e))))),
                AssessedProvenance.FromLiterature(RadialSource),
                Blocks(Paragraph(Text("For every real amplitude n, unit direction e, ordered unit dictionary D and nonnegative lambda, taking the infimum over all coordinatewise nonnegative codes preserves the radial floor. The zero code supplies a nonempty family. For a nonzero signal x, set n to its norm and e to x divided by its norm. For n>lambda>0 this is the classical proximal radial lower bound of Parikh and Boyd, Section 6.5.1; the present statement retains the same floor for all real n and lambda>=0 in arbitrary real inner-product spaces, without asserting attainment."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-slot-matching-from-separate-witnesses"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.two_slot_matching_from_separate_witnesses"),
                H("Separated directions occupy different slots"),
                StatementSource.FromAuthor(Disp(Flow(D(2),delta,Le,Call("dist",u,w),Comma,Exists,i,Comma,Call("dist",Sub(d,i),u),Lt,delta,Comma,Exists,i,Comma,Call("dist",Sub(d,i),w),Lt,delta,Rightarrow,Match()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In any pseudometric space, for any ordered two-entry map D, targets u and w and real tolerance delta, separation by at least twice delta and one nearby entry for each target imply simultaneous matching in the identity or swapped order. The triangle inequality excludes using the same slot for both targets."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quantitative-two-slot-matching"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.quantitative_two_slot_matching"),
                H("Quantitative simultaneous matching"),
                StatementSource.FromAuthor(Disp(Flow(a,Cost(Flow(n,u)),Plus,b,Cost(Flow(m,w)),Lt,a,Radial(n),Plus,b,Radial(m),Plus,Min,Open,a,Gap(n),Comma,b,Gap(m),Close,Rightarrow,Match()))),
                AssessedProvenance.FromRepo(RadialSource),
                Blocks(Paragraph(Text("For arbitrary unit directions u and w in a real inner-product space, positive lambda, amplitudes n and m greater than lambda, positive weights a and b, positive delta and target distance at least twice delta, the displayed strict cost bound forces both slots of the same dictionary to match the two directions. Here g(n,delta) is min((n-lambda)^2/8, lambda(n-lambda)delta^2/4). Square completion bounds the residual, which forces code mass above (n-lambda)/2; atoms all outside the direction ball would then contribute too much correlation defect. Applying this single-direction estimate to each sample and excluding a shared slot yields the simultaneous matching relation. This quantitative two-direction extension uses the classical radial floor but supplies a dictionary-independent gap and a match for both columns."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("code-cost-eq-radial-iff"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_eq_radial_iff"),
                H("Equality detects an aligned atom"),
                StatementSource.FromAuthor(Disp(Flow(Cost(Flow(n,e)),Eq,Radial(),Iff,Exists,i,Comma,Sub(d,i),Eq,e))),
                AssessedProvenance.FromRepo(RadialSource),
                Blocks(Paragraph(Text("For every unit direction e, ordered unit dictionary D, positive lambda and n greater than lambda, equality in the actual infimal radial cost holds exactly when one dictionary atom equals e. The radial value and aligned soft-threshold coefficient are the known proximal core of Parikh and Boyd, Section 6.5.1; the dictionary-level iff corresponds to the alignment criterion of the fiber-law volume's Lemma 4.1, here in an arbitrary real inner-product space. Necessity uses the positive minimum of the two atom distances and the single-direction near-radial estimate; sufficiency uses the single active coefficient n-lambda. This argument does not use simultaneous two-slot matching. It gives the radial equality criterion for every nonzero x with lambda less than its norm."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("whitebox-quantitative-matching"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.whitebox_quantitative_matching"),
                H("Orthogonal samples and an explicit positive gap"),
                StatementSource.FromAuthor(Disp(Flow(D(0),Lt,Call("kappa",delta),Land,Open,Sub(F.Id("J"),D(0)),Open,F.Id("D"),Close,Lt,F.Id("B"),Plus,Call("kappa",delta),Rightarrow,Match(),Close))),
                AssessedProvenance.FromRepo(RadialSource, MergingSource),
                Blocks(Paragraph(Text("Let u and v be orthogonal unit vectors, w=(u+v)/sqrt(2), zero-weight objective J0=a C(u,D)+b C(u+v,D), and B=a(lambda-lambda^2/2)+b(sqrt(2)lambda-lambda^2/2). For 0<lambda<1/sqrt(2), a,b>0 and 0<delta<norm(u-w)/2, kappa(delta)=min(a g(1,delta),b g(sqrt(2),delta)) is positive. Every ordered unit dictionary with J0<B+kappa(delta) has both atoms within delta of u and w, in one of the two orders. Repeated, antipodal and off-plane atoms are included in the domain. The baseline uses the classical proximal radial values; the explicit positive kappa and simultaneous matching strengthen the zero-weight merging characterization recorded in MAIS-A3."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-bounds"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.perturbation_bounds"),
                H("Uniform perturbation bound"),
                StatementSource.FromAuthor(Disp(Flow(Sub(F.Id("J"),D(0)),Open,F.Id("D"),Close,Le,Sub(F.Id("J"),t),Open,F.Id("D"),Close,Le,Sub(F.Id("J"),D(0)),Open,F.Id("D"),Close,Plus,Frac,Grp(t),Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real weights a and b, any u, unit v, ordered unit dictionary D, lambda>=0 and t>=0, J0(D)<=Jt(D)<=J0(D)+t/2. Nonnegativity of the code energy gives the lower bound, and the zero code gives C(v,D)<=1/2."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-global-minima"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.zero_global_minima"),
                H("The exact unperturbed minima"),
                StatementSource.FromAuthor(Disp(Flow(F.Id("B"),Le,Sub(F.Id("J"),D(0)),Open,F.Id("D"),Close,Land,Open,Sub(F.Id("J"),D(0)),Open,F.Id("D"),Close,Eq,F.Id("B"),Iff,ExactMatch(),Close))),
                AssessedProvenance.FromLiterature(MergingSource),
                Blocks(Paragraph(Text("For orthogonal unit u and v, 0<lambda<1/sqrt(2) and a,b>0, every ordered unit dictionary has J0 at least B. Equality holds precisely at the ordered dictionaries (u,w) and (w,u), where w=(u+v)/sqrt(2). The canonical dictionary realizes B, so these are exactly the global minimizers. This is the two-atom zero-weight merging core attested by the Positive-penalty merging proposition of MAIS-A3, a research draft, expressed here for arbitrary real inner-product spaces and the stated penalty range. Positive weights force both radial terms to attain equality; the single-direction equality criterion identifies each aligned atom, and distinctness forces different slots. The proof uses that criterion and its single-direction estimate, without invoking the simultaneous near-equality matching theorem."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-positive-minimizers-localize"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.small_positive_minimizers_localize"),
                H("All small positive-weight minimizers localize"),
                StatementSource.FromAuthor(Disp(Flow(Forall,delta,Gt,D(0),Comma,Exists,F.Id("eta"),Gt,D(0),Comma,Forall,t,Comma,D(0),Lt,t,Lt,F.Id("eta"),Rightarrow,Call("argmin",Sub(F.Id("J"),t),F.Id("D")),Rightarrow,Match()))),
                AssessedProvenance.FromRepo(RadialSource, MergingSource),
                Blocks(Paragraph(Text("For orthogonal unit u and v, 0<lambda<1/sqrt(2), positive a,b and a+b<1, every positive tolerance delta admits eta>0 such that for every 0<t<eta and every ordered unit dictionary D minimizing Jt over all ordered unit dictionaries, D lies within delta of (u,w) or (w,u). One may take epsilon=min(delta,norm(u-w)/4) and eta=min(kappa(epsilon),1-a-b). Comparing with the canonical dictionary gives J0(D)<=B+t/2, so the simultaneous quantitative matching theorem applies. This extends the literature-attested zero-weight merging core to uniform localization for small positive weights through the explicit matching gap. It is a universal statement about every minimizer and does not assert existence for t>0."))), DescribeRole.Theorem))));
}
