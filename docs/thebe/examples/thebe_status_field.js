// Functions for the thebe activate button and status field

function thebe_place_activate_button() {
  $(".thebe_status_field").html(
    '<input type="button"\
                  onclick="thebe_activate_button_function()"\
                  value="Activate"\
                  title="Thebe (requires internet):\nClick to activate code cells in this page.\nYou can then edit and run them.\nComputations courtesy of mybinder.org."\
                   class="thebe-status-field"/>'
  );
}

function thebe_remove_activate_button() {
  $(".thebe_status_field").empty();
}

function thebe_place_status_field() {
  $(".thebe_status_field").html(
    '<span class="thebe-status-field"\
                title="Thebe status.\nClick `run` to execute code cells.\nComputations courtesy of mybinder.org.">\
          </span>'
  );
}

function thebe_activate_cells() {
  // Download thebe
  thebelab.on("status", function (evt, data) {
    console.log("Status changed:", data.status, data.message);
    $(".thebe-status-field")
      .attr("class", "thebe-status-field thebe-status-" + data.status)
      .text(data.status);
  });
  thebelab.bootstrap();
}

// Activate button function hook
function thebe_activate_button_function() {
  // Load the Thebe library
  $.getScript("https://unpkg.com/thebelab@latest")
    .done(function (script, textStatus) {
      thebe_remove_activate_button();
      thebe_place_status_field();
      thebe_activate_cells();
    })
    .fail(function (jqxhr, settings, exception) {
      $("div.log").text("Could not fetch Thebe library.");
    });
}
