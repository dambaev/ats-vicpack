#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
staload "./../SATS/vicpack.sats"

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload "{$LIBS}/ats-bytestring/SATS/bytestring.sats"

%{^
#include "arpa/inet.h"
%}

implement free_vicpack( i) =
  case+ i of
  | ~driver_info_vt(_) => ()
  | ~internal_battery_on_die_vt(_) => ()
  | ~internal_battery_vt(_) => ()
  | ~internal_temperature_vt(_) => ()
  | ~charge_vt(_) => ()
  | ~temperature_vt(_) => ()
  | ~humidity_vt(_) => ()
  | ~presure_vt(_) => ()
  | ~acceleration_x_vt(_) => ()
  | ~acceleration_y_vt(_) => ()
  | ~acceleration_z_vt(_) => ()
  | ~switch_interrupt_vt(_) => ()
  | ~audio_average_vt(_) => ()
  | ~audio_max_vt(_) => ()
  | ~audio_spl_vt(_) => ()
  | ~ambient_light_visible_vt(_) => ()
  | ~ambient_light_ir_vt(_) => ()
  | ~ambient_light_uv_vt(_) => ()
  | ~co2_level_vt(_) => ()
  | ~distance_vt(_) => ()
  | ~sample_rate_vt(_) => ()
  | ~voc_iaq_vt(_) => ()
  | ~voc_temperature_vt(_) => ()
  | ~voc_humidity_vt(_) => ()
  | ~voc_pressure_vt(_) => ()
  | ~voc_ambient_light_vt(_) => ()
  | ~voc_sound_peak_vt(_) => ()
  | ~tof_distance_vt(_) => ()
  | ~accelerometer_status_vt(_) => ()
  | ~voltage_vt(_) => ()
  | ~voltage_dff_vt(_) => ()
  | ~voltage_ref_vt(_) => ()
  | ~falling_counter_vt(_) => ()
  | ~rising_counter_vt(_) => ()
  | ~gps_data_vt(_) => ()
  | ~eco2_vt(_) => ()
  | ~device_id_vt(_) => ()
  | ~device_pin_vt(_) => ()
  | ~rssi_level_vt(_) => ()
  | ~cell_id_vt(_) => ()

(* converts integer to byte *)
extern castfn
  i2uc
  {n: nat | n <= 255}
  ( i: int n
  ):<> uchar(n)
  
extern castfn
  uc2i
  ( i: uchar
  ):<> int

implement parse( s) =
let
  prval () = lemma_bytestring_param(s)
  fun
    parse_packages
    {n,ln : nat | n <= 255}
    {ilen,ioffset,cap,ucap,refcnt:nat | ilen >= n * 5}{dynamic:bool}{l:addr}
    .<n>.
    ( i: size_t n
    , acc: list_vt( Vicpack, ln)
    , s: &($BS.Bytestring_vtype(ilen, ioffset, cap, ucap, refcnt, dynamic, l)) >> Bytestring_vtype( olen, ooffset, cap, ucap, refcnt, dynamic, l)
    ):
    #[olen,ooffset,oln: nat]
    list_vt( Vicpack, oln) =
    ifcase
    | i = i2sz 0 => acc
    | $BS.length s < i2sz 5 => acc
    | _ =>
    let
      var package_s: $BS.Bytestring0?
      val () = package_s := $BS.take( i2sz 5, s)
      val () = s := $BS.dropC( i2sz 5, s)
    in
      case+ parse_package package_s of
      | ~None_vt() => parse_packages( i - i2sz 1, acc, s) where {
        val () = $BS.free( package_s, s)
      }
      | ~Some_vt( package) => parse_packages( i - i2sz 1, list_vt_cons( package, acc), s) where {
        val () = $BS.free( package_s, s)
      }
    end
  var i: $BS.Bytestring0?
  val () = i := $BS.ref_bs_parent s
  val () = i := $BS.dropC( i2sz 5, i) // without header
  val packages_count_i = g1ofg0( uc2i( s[4]))
in
  if packages_count_i < 0
  then list_vt_nil() where {
    val () = $BS.free( i, s)
  }
  else
  let
    val packages_count = i2sz packages_count_i
  in
    ifcase
    | s[0] != i2uc 0xFA => list_vt_nil() where {
      val () = $BS.free( i, s)
    }
    | packages_count > 255 => list_vt_nil() where {
      val () = $BS.free( i, s)
    }
    | $BS.length i < packages_count * (i2sz 5) => list_vt_nil() where {
      val () = $BS.free( i, s)
    }
    | _ => res where {
      val res = parse_packages( packages_count, list_vt_nil(), i)
      val () = $BS.free( i, s)
    }
  end
end

fn
  uc2bool (i: uchar):<> bool =
case+ uc2i i of
| 0 => false
| _ => true

extern fn
  ntohl
  (i: uint32
  ):<> uint32 = "mac#"

extern prfun
  bytes_takeout
  {a:t0ype}{n: nat}{l:addr}
  ( i: !(bytes(n) @ l) >> ( bytes(n) @ l, a @ l)
  ):<>
  a @ l

extern prfun
  bytes_addback
  {a:t0ype}{n: nat}{l:addr}
  ( i: !( bytes(n) @ l, a @ l) >> (bytes(n) @ l)
  , i1: a @ l
  ):<> void

extern castfn
  u322double( i: uint32):<> double

extern castfn
  u322uint( i: uint32):<> uint

extern castfn
  i2u32
  {n: nat}
  ( i: int n):<> uint32

implement parse_package( s) =
let
  prval () = $BS.lemma_bytestring_param( s)
  val package_type = uc2i( s[0])
in
  case+ package_type of
  | 0x01 => Some_vt( driver_info_vt( @{ is_enabled=uc2bool( s[1]), index=s[2], slot=s[3], type=s[4]}))
  | 0x07 => Some_vt( internal_battery_on_die_vt( result )) where {
    var data: $BS.Bytestring0?
    val () = data := ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val result = ntohl netdata
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
  }
  | 0x14 => Some_vt( temperature_vt(result )) where {
    var data: $BS.Bytestring0?
    val () = data := ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val raw = ntohl netdata
    val result = u322double( raw) * 175.72 / 65536.0 - 46.85
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
  }
  | 0x15 => Some_vt( humidity_vt(result )) where {
    var data: $BS.Bytestring0?
    val () = data := ref_bs_parent s
    val () = data := $BS.dropC( i2sz 1, data)
    val ( pf | ptr, sz) = $BS.bs2bytes data
    prval pf1 = bytes_takeout{uint32}( pf )
    val netdata = !ptr
    val result = g0uint_sub_uint32( g0uint_div_uint32( g0uint_mul_uint32((ntohl netdata), i2u32(125)), i2u32(65536)), i2u32(6))
    prval () = bytes_addback( pf, pf1)
    val data1 = minus_addback( pf | data)
    val () = data := data1
    val () = $BS.free( data, s)
  }
  | _ => None_vt() where {
    val () = println!( "no parser for ", package_type )
  }
end

implement print_vicpack( i) =
  case+ i of
  | driver_info_vt( s) =>
    println!( "DRIVER_INFO: is_enabled = ", s.is_enabled, ", index=", uc2i s.index, ", slot=", uc2i s.slot, ", type=", uc2i s.type)
  | internal_battery_on_die_vt(_) =>
    println!("internal_battery_on_die")
  | internal_battery_vt(_) =>
    println!("internal_battery")
  | internal_temperature_vt(_) =>
    println!("internal_temperature")
  | charge_vt(_) =>
    println!("charge")
  | temperature_vt( value) =>
    println!("temperature: ", value)
  | humidity_vt( value) =>
    println!("humidity: ", value)
  | presure_vt(_) =>
    println!("presure")
  | acceleration_x_vt(_) =>
    println!("acceleration_x")
  | acceleration_y_vt(_) =>
    println!("acceleration_y")
  | acceleration_z_vt(_) =>
    println!("acceleration_z")
  | switch_interrupt_vt(_) =>
    println!("switch_interrupt")
  | audio_average_vt(_) =>
    println!("audio_average")
  | audio_max_vt(_) =>
    println!("audio_max")
  | audio_spl_vt(_) =>
    println!("audio_spl")
  | ambient_light_visible_vt(_) =>
    println!("ambient_light_visible")
  | ambient_light_ir_vt(_) =>
    println!("ambient_light_ir")
  | ambient_light_uv_vt(_) =>
    println!("ambient_light_uv")
  | co2_level_vt(_) =>
    println!("co2_level")
  | distance_vt(_) =>
    println!("distance")
  | sample_rate_vt(_) =>
    println!("sample_rate")
  | voc_iaq_vt(_) =>
    println!("voc_iaq")
  | voc_temperature_vt(_) =>
    println!("voc_temperature")
  | voc_humidity_vt(_) =>
    println!("voc_humidity")
  | voc_pressure_vt(_) =>
    println!("voc_pressure")
  | voc_ambient_light_vt(_) =>
    println!("voc_ambient_light")
  | voc_sound_peak_vt(_) =>
    println!("voc_sound_peak")
  | tof_distance_vt(_) =>
    println!("tof_distance")
  | accelerometer_status_vt(_) =>
    println!("accelerometer_status")
  | voltage_vt(_) =>
    println!("voltage")
  | voltage_dff_vt(_) =>
    println!("voltage_dff")
  | voltage_ref_vt(_) =>
    println!("voltage_ref")
  | falling_counter_vt(_) =>
    println!("falling_counter")
  | rising_counter_vt(_) =>
    println!("rising_counter")
  | gps_data_vt(_) =>
    println!("gps_data")
  | eco2_vt(_) =>
    println!("eco2")
  | device_id_vt(_) =>
    println!("device_id")
  | device_pin_vt(_) =>
    println!("device_pin")
  | rssi_level_vt(_) =>
    println!("rssi_level")
  | cell_id_vt(_) =>
    println!("cell_id")
