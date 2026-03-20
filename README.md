# dahlia
heap models in dafny

the project that will not die

this is a snapshot of a work-in-progress,
attempting to reintegrate various results built seperately.

Should the paper be accepted, revised and refactored source will be
submitted to ACM's artefact evaluation and archiving.

this version has not yet been packaged as an artefact

to attempt to verify or run:  goto the dafny web page here
https://github.com/dafny-lang/dafny/releases/

select 'Assets'
scroll down to a recent release such as nightly-2026-03-17-b262447
install the zip file
run the "allow on a mac" script if you're on a mac

files should at least resolve with dafny resolve --general-newtypes=false  --type-system-refresh=false  foo.dfy

many will verify. some will not.   there are a few "assumes" scattered
around. they are mostly either in debugging code, or covering up for
persistent Dafny bugs. (eg the one in the Library.dfy)

Individual files can easily 10+ minutes to verify on my machine at least.



                                          .,     .'....d...... . ......... ..'......                         
                                         ...     ........'......''''''':;.'','......                         
              ''... ..              .    ....      ......',',,;;,:l:,;:;,,,,'.....'..                        
               .'.   ........',,,,,,;:::::c:'..   .,;'..''',',;,';;;,,,,''''......'.......    ...            
                    .....,,',;;,,::ccccc::cc:'.. .,coddc'...:'.',','.''''............                        
              ..   ......';,,,,;,,;;;;;;,,,'','.. .:lllc.  ...,,'''''.........                               
  .           .     ....',;;,,''''';,,,''',;'''.  'colll... ............  ...                                
  .                   .';;'....',;,,''.,;:c:'.   .';;,;c;,............                                       
              .         ...............;;..      .:,...';;,'..'.                                             
                            ..  .     ,'....  . ..,,.,l;c:,'...'
                                         take                          
                                        ........,,;cc:clc;'....;                                             
                                           .....',..clll:;''...                                              
                                              .'.......c:,'.                                                 
                                                 ';';;,,'..                                                  
                                                 o,,;:;....;;.                                               
                          .                    ..kO;....:dxdc.                                               
                                      ..         x:::;,.'ldo:                                                
                                                 cdko...odll.                                                
                                                 xxkc...okko                                                 
                                                 okd:'..;xk:                                                 
                                                 ;x:,;;',kk.                                                 
                                                 .x,..,;;xo                                                  
                              ..                  d;'..',x;      l.                                          
                             ..                   cc;,'..x.   ...;...                                        
           ,                                      .ccc;'.k   .',;;.;..                                       
          dk                                       .;cc:'x   ..',,','                                        
         cK.                                       .'coold,               ..                                 
        'X'                               ,:lcc:cdkxxxoodoc.           .cxxxdxo:,;:c'                        
        0:                              .x0xoxxxkxddxdlll:,'          .Okxkkkkko..',x:                       
       xo.                              lkc:dddolooodl:cc,l;          ,oodxddddc....:.                       
     .:K;.                         '.,  .kx.;:c:cllloc;::,lc            ::olldxc... ., .'     ...............
