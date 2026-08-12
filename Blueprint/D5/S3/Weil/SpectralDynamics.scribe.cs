using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class SpectralDynamicsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef HedenmalmHilbert =
        LibraryNoteRef.Create("D5/L/hedenmalm1997hilbert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient dynamics and zero resonance align spectral geometry on the O-6 path.",
        H("Spectral Dynamics Toward Weil Positivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vertical-evolution-is-a-norm-preserving-group"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group"),
                H("Vertical evolution is a norm-preserving group"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("t"), Comma, F.Id("u"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, Forall, Sp, F.Id("x"), InMacro, Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc, F.Id("V"), Underscore, Grp(D(0)), F.Id("x"), Eq, F.Id("x"), Sp, Land, Sp, F.Id("V"), Underscore, Grp(F.Id("t"), Plus, F.Id("u")), F.Id("x"), Eq, F.Id("V"), Underscore, Grp(F.Id("t")), Open, F.Id("V"), Underscore, Grp(F.Id("u")), F.Id("x"), Close, Sp, Land, Sp, F.Id("V"), Underscore, Grp(Minus, F.Id("t")), Open, F.Id("V"), Underscore, Grp(F.Id("t")), F.Id("x"), Close, Eq, F.Id("x"), Sp, Land, Sp, Vert, Sp, F.Id("V"), Underscore, Grp(F.Id("t")), F.Id("x"), Vert, Eq, Vert, Sp, F.Id("x"), Vert))),
                AssessedProvenance.FromLiterature(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                                    "Multiplication of each coefficient by n to the power -it gives the identity, composition, inverse, and norm-preservation laws on the square-summable coefficient space. The declaration proves those laws directly for the coordinate multiplier; it does not introduce an unbounded self-adjoint length operator, bundle a continuous linear unitary equivalence, or prove strong continuity or a generator theorem."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("forward-horizontal-evolution-is-a-contraction-semigroup"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.horizontal_evolution_contraction_semigroup"),
                H("Forward horizontal evolution is a contraction semigroup"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, DeltaLower, Comma, Varepsilon, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, DeltaLower, Geq, Sp, D(0), Sp, Land, Sp, Varepsilon, Geq, Sp, D(0), Sp, Rightarrow, Sp, Forall, Sp, F.Id("x"), InMacro, Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc, F.Id("H"), Underscore, Grp(D(0)), F.Id("x"), Eq, F.Id("x"), Sp, Land, Sp, F.Id("H"), Underscore, Grp(DeltaLower, Plus, Varepsilon), F.Id("x"), Eq, F.Id("H"), Underscore, Grp(DeltaLower), Open, F.Id("H"), Underscore, Grp(Varepsilon), F.Id("x"), Close, Sp, Land, Sp, Vert, Sp, F.Id("H"), Underscore, Grp(DeltaLower), F.Id("x"), Vert, Leq, Vert, Sp, F.Id("x"), Vert))),
                AssessedProvenance.FromLiterature(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                                    "For nonnegative real increments, multiplication of the nth coefficient by n to the power -delta gives identity and composition laws and cannot increase the square-summable norm. Only this bounded forward direction is bundled. The declaration does not define the reverse unbounded operator or characterize the domain of a multiplier by n to the power delta."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("labeled-zeta-vectors-follow-the-coordinate-evolutions"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.labeled_zeta_evolution_spec"),
                H("Labeled zeta vectors follow the coordinate evolutions"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, SigmaLower, Comma, SigmaLower, Apos, Comma, F.Id("t"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, Frac, Grp(D(1)), Grp(D(2)), Lt, SigmaLower, Sp, Land, Sp, SigmaLower, Leq, SigmaLower, Apos, Sp, Rightarrow, Sp, F.Id("V"), Underscore, Grp(F.Id("t")), Operatorname, Grp(F.Id("labeledZetaVector")), Open, SigmaLower, Close, Eq, Operatorname, Grp(F.Id("labeledZetaVector")), Open, SigmaLower, Plus, F.Id("it"), Close, Sp, Land, Sp, F.Id("H"), Underscore, Grp(SigmaLower, Apos, Minus, SigmaLower), Operatorname, Grp(F.Id("labeledZetaVector")), Open, SigmaLower, Plus, F.Id("it"), Close, Eq, Operatorname, Grp(F.Id("labeledZetaVector")), Open, SigmaLower, Apos, Plus, F.Id("it"), Close))),
                AssessedProvenance.FromLiterature(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                                    "A labeled zeta vector to the right of the half-density boundary is carried from sigma to sigma + it by the vertical multiplier. If sigma is at most sigma prime, the bounded horizontal multiplier then carries it to sigma prime + it. The ordering hypothesis makes the source's forward dissipative direction explicit; no reverse-domain identity is asserted."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("zero-symmetries-form-the-kernel-resonant-cross-pairs"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec"),
                H("Zero symmetries form the kernel-resonant cross-pairs"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("Z"), Colon, Operatorname, Grp(F.Id("ZeroData")), Comma, Esc, Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("Z"), Underscore, Grp(F.Id("C"), Open, F.Id("R"), Open, F.Id("n"), Close, Close), Eq, D(1), Minus, Overline, Grp(F.Id("Z"), Underscore, Grp(F.Id("n"))), Sp, Land, Sp, Operatorname, Grp(F.Id("KernelResonant")), Open, F.Id("Z"), Underscore, Grp(F.Id("n")), Comma, F.Id("Z"), Underscore, Grp(F.Id("C"), Open, F.Id("R"), Open, F.Id("n"), Close, Close), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("KernelResonant")), Open, F.Id("Z"), Underscore, Grp(F.Id("C"), Open, F.Id("n"), Close), Comma, F.Id("Z"), Underscore, Grp(F.Id("R"), Open, F.Id("n"), Close), Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("w"), Comma, Esc, Operatorname, Grp(F.Id("KernelResonant")), Open, F.Id("Z"), Underscore, Grp(F.Id("n")), Comma, F.Id("w"), Close, Sp, Leftrightarrow, Sp, F.Id("w"), Eq, F.Id("Z"), Underscore, Grp(F.Id("C"), Open, F.Id("R"), Open, F.Id("n"), Close, Close), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The existing reflection and conjugation permutations send every enumerated nontrivial zero to its unique partner for the equation s plus conjugate w equals one, and the two cross-pairs satisfy that equation. The declaration is conditional on a supplied ZeroData value. The repository does not prove that ZeroData is inhabited: no instance or example exists. Accordingly this conditional theorem does not close the source corollary unconditionally; that source obligation remains open. This strengthens the conditional conclusion from off-line zeros to all enumerated zeros, so it permits degenerate critical-line configurations and asserts no pairwise distinct quartet. Resonance here is only the kernel equation, not a new analytic pole or continuation theorem."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("critical-line-predicates-use-one-abscissa"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.critical_line_characterizations"),
                H("Critical-line predicates use one abscissa"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Open, Exists, Sp, F.Id("a"), Comma, Ell, Open, F.Id("a"), Close, Neq, Sp, D(0), Close, Sp, Rightarrow, Sp, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, F.Id("s"), Eq, Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close, Leftrightarrow, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Close, Sp, Land, Sp, Open, Open, Forall, Sp, F.Id("a"), Comma, Vert, Operatorname, Grp(F.Id("halfDensityReading")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Vert, Eq, D(1), Close, Leftrightarrow, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Close, Sp, Land, Sp, Open, F.Id("s"), Plus, Overline, Grp(F.Id("s")), Eq, D(1), Leftrightarrow, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Close, Sp, Land, Sp, Open, Operatorname, Grp(F.Id("MemLp")), Open, Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open, F.Id("s"), Close, Comma, D(2), Close, Leftrightarrow, Frac, Grp(D(1)), Grp(D(2)), Lt, Re, Open, F.Id("s"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For any additive ledger with a nonzero length, mirror fixed points, unit-modulus half-density readings, and self-resonance all select real part one half. The labeled zeta coefficient is square-summable exactly on the strict right half-plane, exposing one half as its boundary without asserting endpoint membership. The combined statement locates no zeta zero and adds no Riemann-hypothesis conclusion."))),
                DescribeRole.Theorem
            ),
            Describe.Remark(
                DescribeId.Create("diagonal-flow-and-generator-boundary"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group"),
                H("Diagonal flow and the generator boundary"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate multiplier has logarithmic frequencies, but the checked declaration supplies only its group and norm laws. It does not construct a self-adjoint operator whose spectrum is the zeta zeros; that Hilbert-Polya step remains outside this module.")))),
            Describe.Remark(
                DescribeId.Create("two-regimes-and-two-directions"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.critical_line_characterizations"),
                H("Two regimes and two directions"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The square-summable side is the strict half-plane to the right of one half. Vertical evolution is reversible and norm-preserving, while the formal horizontal evolution is only a forward contraction. Reading these as two phases or two times is a narrative synthesis, not a functional equation or a zero-location theorem.")))),
            Describe.Remark(
                DescribeId.Create("phase-delay-is-not-address-delay"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group"),
                H("Phase delay is not address delay"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vertical multiplier records reversible phase accumulation. A discrete walk needed to reach an address is a different notion of delay, and this declaration neither identifies the two nor assigns an intrinsic time offset between parallel coefficient flows.")))),
            Describe.Remark(
                DescribeId.Create("off-line-pairs-remain-conditional"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec"),
                H("Off-line pairs remain conditional"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For supplied zero data, mirror and conjugation organize entries into the checked cross-pairs. The declaration does not establish that such data exists, that an off-line entry occurs, or that a paired entry has decay, lifetime, or probabilistic meaning.")))),
            Describe.Remark(
                DescribeId.Create("counting-does-not-locate-real-parts"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec"),
                H("Counting does not locate real parts"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conditional partner equations preserve the supplied inventory but do not determine the real coordinate of any entry. Argument-principle counts, collision dynamics, and the existence of zero data are separate obligations not discharged here.")))),
            Describe.Remark(
                DescribeId.Create("equalities-do-not-supply-positivity"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.critical_line_characterizations"),
                H("Equalities do not supply positivity"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Symmetry equations and the shared half-density coordinate do not imply Li or Weil positivity and therefore do not locate zeros. Metaphors that separate reversible phase time from irreversible ledger time remain explanatory readings rather than additional formal conclusions.")))),
            Describe.Remark(
                DescribeId.Create("speculative-off-line-effects-are-not-formalized"),
                DeclarationHandle.Create("D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec"),
                H("Speculative off-line effects are not formalized"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The checked zero-data result records only permutations and resonance equations. Detection scales, thermal lifetimes, causal effects on prime counting, and physical interpretations of hypothetical off-line entries are not claims of this module.")))),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("thermal-time-is-a-meta-time-not-a-physical-history"),
                H("Thermal time is a meta-time, not a physical history"),
                DescribeStatement.FromFormula(Equal(
                    new Formula.Subscript(DefinitionDsl.Id("H"), Num(0)),
                    DefinitionDsl.Id("Xi"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Three ingredients explain the source's thermal imagery. First, the Connes-Rovelli thermal-time hypothesis identifies physical time with the modular flow generated by a state; the source treats its de Bruijn-Newman time as an arithmetic analogue and notes that modular flow is also the Bost-Connes time evolution associated there with unitary scaling. Second, it offers only a heuristic that critical physical systems exhibit universal fluctuations, random-matrix statistics are a standard universality class, and GUE zero statistics might therefore be related to the critical value Lambda = 0. That relation is marked unproved. Third, the source supplies the limiting correction: de Bruijn-Newman time parametrizes a family of systems rather than the physical evolution of one system. H_0 = Xi is the actual object by definition, while t > 0 gives mathematical deformations. The claimed present moment is therefore the name of the undeformed system, not evidence that a universe selected one time on the heat axis.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("causal-direction-requires-irreversible-bookkeeping"),
                H("Causal direction requires irreversible bookkeeping"),
                DescribeStatement.FromFormula(Equal(
                    DefinitionDsl.Id("causality"),
                    Multiply(DefinitionDsl.Id("logic"), DefinitionDsl.Id("irreversibility")))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source presents an internal self-model in which evolution factors into orthogonal operations, classification, and bookkeeping. It assigns new axes to orthogonal pairing and convolution, two complementary halves to classification, and the growth of the ledger to time; this description is expressly not claimed for the external world. It then corrects the slogan that logic alone gives causality. Logic has no tense and reversible phase time has no arrow; causal direction appears only in the ledger layer, fueled by monotone cost. Hence its formula is causality = logic * irreversibility, with a minimal demonstration in which the same rule has a directionless period-two reversible implementation but a strictly growing bookkeeping implementation that orders events. Finally, the Pythagorean claim that everything is number is classified as a normative choice rather than a truth-valued proposition. The internal kernel may be considered a self-contained universe model, but whether the external world is that model is kept outside the classification scheme and deliberately left undecided.")))
            )),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S3/Weil/CriticalLine")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S3/Weil/SpectralHilbert")),
                    ]));
}
