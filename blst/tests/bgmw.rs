#[cfg(test)]
mod tests {
    use std::{path::PathBuf, ffi::{CString, CStr}};

    use blst::{blst_p1_generator, blst_p1_affine, blst_p1_double, blst_p1_to_affine, blst_p1_affine_compress, blst_fp};
    use rust_kzg_blst::bgmw;

    #[test]
    fn bgmw_precomputation_test(){
        struct Fixture {
            name: String,
            message: String,
        }
    
        let fixtures = [
            Fixture {
                name: "valid_p1_generator_bgmw_precomputation".to_string(),
                message: "Really bad :^(".to_string(),
            },
        ];
    
        for fixture in fixtures {
            let filename = "bgmw_precomp.txt";

            let file_path = PathBuf::from("../blst/")
                        .join("tests/fixtures")
                        .join(fixture.name)
                        .join(filename)
                        .as_os_str()
                        .to_str()
                        .unwrap()
                        .to_string();
            
            let file = unsafe {
                let c_file_path = CString::new(file_path.clone()).unwrap();
                libc::fopen(
                    c_file_path.as_ptr(),
                    CStr::from_bytes_with_nul_unchecked(b"r\0").as_ptr(),
                )
            };
    
            assert!(!file.is_null());
            let mut buf = vec![0u8; 2166784]; //failo dydis 
            let len: usize = unsafe { libc::fread(buf.as_mut_ptr() as *mut libc::c_void, 1, buf.len(), file) };
            let s = match String::from_utf8(buf[..len].to_vec()){ 
                Ok(value) => value,
                Err(_) => String::from("sad"),
            };
            let mut offset = 0;
            #[inline(always)]
            fn scan_number(offset: &mut usize, contents: &str) -> Result<usize, String> {
                *offset += contents[(*offset)..]
                    .find(|c: char| !c.is_whitespace())
                    .ok_or_else(|| String::from("sad"))?;
                let start = *offset;
                *offset += contents[(*offset)..]
                    .find(|c: char| !c.is_ascii_digit())
                    .ok_or_else(|| String::from("sad"))?;
                let end = *offset;
                contents[start..end]
                    .parse::<usize>()
                    .map_err(|_| String::from("sad"))
            }

            let point_count = match scan_number(&mut offset, &s){
                Ok(value) => value,
                Err(_) => 0,
            };
            
            let mut bytes = vec![0u8; point_count * 48];

            #[inline(always)]
            fn scan_hex_byte(offset: &mut usize, contents: &str) -> Result<u8, String> {
                *offset += contents[(*offset)..]
                    .find(|c: char| !c.is_whitespace())
                    .ok_or_else(|| String::from("sad"))?;
                let start = *offset;

                let end = if contents
                    .get((*offset + 1)..)
                    .map(|it| {
                        it.chars()
                            .next()
                            .map(|c| c.is_ascii_hexdigit())
                            .unwrap_or(false)
                    })
                    .unwrap_or(false)
                {
                    *offset += 2;
                    *offset
                } else {
                    *offset += 1;
                    *offset
                };

                u8::from_str_radix(&contents[start..end], 16).map_err(|_| String::from("sad"))
            }

            for byte in &mut bytes {
                *byte = match scan_hex_byte(&mut offset, &s) {
                    Ok(value) => value,
                    Err(_) => 0,
                };
            }  
            let mut computed = vec![blst_p1_affine::default(); point_count];
            let mut fix_points_list = vec![blst_p1_affine::default(); 1024];
            let mut blst_p1;
            unsafe {
                blst_p1 = *blst_p1_generator();
            }
            let mut tmp_p_affine: blst_p1_affine = blst_p1_affine::default();
            unsafe {
                for i in 0..1024{
                    let blst_p1_tmp = blst_p1;
                    blst_p1_double(&mut blst_p1, &blst_p1_tmp);
                    blst_p1_to_affine(&mut tmp_p_affine, &blst_p1);
                    fix_points_list[i] = tmp_p_affine;
                }
            }

            bgmw::init_pippenger_bgmw(&mut computed, fix_points_list.as_slice());
    
            unsafe {
                libc::fclose(file);
            }
            for i in 0..point_count{
                let mut temps = [0u8; 48];
                unsafe{
                    blst_p1_affine_compress(temps.as_mut_ptr(), &computed[i])
                }
                assert!(
                    bytes[i*48..i*48+48] == temps,
                    "{}, fixture: {file_path}",
                    fixture.message
                );   
            }
        }
    }
    #[test]
    fn single_scalar_multiplication_test(){
        let scalar: usize = 2; 
        let mut test: blst_p1_affine = blst_p1_affine 
        { x: blst_fp { l: [6046496802367715900, 4512703842675942905, 5557647857818872160, 11911007586355426777, 2789226406901363231, 2402832991291269] }, 
        y: blst_fp { l: [8075247918781118784, 15723127573743364860, 13289805640942397317, 12593984073093990549, 2724610382811436832, 447576566110657301] } };

        test = bgmw::single_scalar_multiplication(scalar, test);

        let truth: blst_p1_affine = blst_p1_affine 
        { x: blst_fp { l: [829396425412873931, 4630191540216922912, 355385700763152750, 14285431475212315696, 805409597614920011, 576608384544293863] }, 
        y: blst_fp { l: [16917084574279409168, 1285895338278983897, 8416868578363461231, 16052080159904405683, 17022798986550011276, 1782778860764068411] } };
        
        assert!(test == truth, "Damn")
    }
}