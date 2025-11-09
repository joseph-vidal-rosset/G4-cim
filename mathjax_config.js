// MathJax Configuration for G4-cim
// Complete Fitch-style proof rendering in MathJax

window.MathJax = {
    tex: {
        inlineMath: [['$', '$'], ['\\(', '\\)']],
        displayMath: [['$$', '$$'], ['\\[', '\\]']],
        processEscapes: true,
        processEnvironments: true,
        
        macros: {
            // Fitch-style proof macros
            fa: '\\mathord{\\rule[-0.5ex]{0.05em}{2.5ex}}\\hspace{0.9em}',
            fb: '\\mathord{\\rule[-0.3ex]{0.05em}{1.2ex}}\\hspace{0.9em}',
            fh: '\\mathord{\\rule[-0.5ex]{0.05em}{1.2ex}\\rule{1.5em}{0.05em}}\\hspace{0.5em}',
            fj: '\\mathord{\\rule[-0.5ex]{0.05em}{2.5ex}\\rule{1.5em}{0.05em}}\\hspace{0.5em}',
            
            // Logic symbols
            land: '\\wedge',
            lor: '\\vee',
            lnot: '\\neg',
            to: '\\rightarrow',
            leftrightarrow: '\\leftrightarrow',
            forall: '\\forall',
            exists: '\\exists',
            bot: '\\bot',
            vdash: '\\vdash',
            
            // Proof tree commands (bussproofs simulation)
            AxiomC: ['\\frac{}{#1}', 1],
            UnaryInfC: ['\\frac{#1}{#2}', 2],
            BinaryInfC: ['\\frac{#1\\quad#2}{#3}', 3],
            TrinaryInfC: ['\\frac{#1\\quad#2\\quad#3}{#4}', 4],
            RightLabel: ['\\,{\\scriptsize #1}\\,', 1],
            LeftLabel: ['\\,{\\scriptsize #1}\\,', 1],
            noLine: ''
        },
        
        packages: {'[+]': ['ams', 'bussproofs']}
    },
    
    options: {
        skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'],
        processHtmlClass: 'tex2jax_process|proof-content'
    },
    
    startup: {
        pageReady() {
            return MathJax.startup.defaultPageReady().then(() => {
                console.log('MathJax ready for G4-cim proofs');
            });
        }
    }
};
